package main

import (
    "container/heap"
    "errors"
    "encoding/binary"
    _ "encoding/hex"
    "log"
    "net"
    "crypto/rand"
    "crypto/sha1"
    "strconv"
    "sync"
    "time"
    "os"
)

const (
    REQ_PING byte =  iota
    REQ_STORE
    REQ_FIND_NODE
    REQ_FIND_VAL
)

const ID_SIZE = 20
// Size of the "k-buckets" i.e. the number of nodes stored for each distance from self
const K = 20
// Maximum number of parallel lookup requests to send at a time
const N_LOOKUP = 3




type BucketEntry struct {
    Id [ID_SIZE]byte
    Addr string
}

/* Priority Queue */
type Item struct {
    entry *BucketEntry
    priority int
    index int
}

type PriorityQueue []*Item

func (pq PriorityQueue) Len() int {
    return len(pq)
}

func (pq PriorityQueue) Less(i, j int) bool {
    return pq[i].priority > pq[j].priority
}

func (pq PriorityQueue) Swap(i, j int) {
    pq[i], pq[j] = pq[j], pq[i]
    pq[i].index = i
    pq[j].index = j
}

func (pq *PriorityQueue) Push(x interface{}) {
    n := len(*pq)
    item := x.(*Item)
    item.index = n
    *pq = append(*pq, item)
}

func (pq *PriorityQueue) Pop() interface{} {
    old := *pq
    n := len(old)
    item := old[n-1]
    item.index = -1
    *pq = old[:n-1]
    return item
}

func (pq *PriorityQueue) Update(item *Item, entry *BucketEntry, priority int) {
    item.entry = entry
    item.priority = priority
    heap.Fix(pq, item.index)
}

/* End Priority Queue */


type Node struct{
    Addr string
    Id [ID_SIZE]byte
    Buckets [ID_SIZE][K]*BucketEntry
    BucketSizes [ID_SIZE]int
    Storage map[[ID_SIZE]byte][]byte
    BucketsLock sync.RWMutex
}


func readExact(c net.Conn, res []byte) (error) {
    n, err := c.Read(res)

    if n != len(res) {
        return errors.New("Number read does not match expected: " + strconv.Itoa(n) + " read vs. " + strconv.Itoa(len(res)) + " expected.")
    }
    return err
}


func writeExact(c net.Conn, toWrite []byte) (error) {
    n, err := c.Write(toWrite)
    if n != len(toWrite) {
        return errors.New("Number written does not match expected: " + strconv.Itoa(n) + " written vs. " + strconv.Itoa(len(toWrite)) + " expected.")
    }
    return err
}


func (n *Node) writeOwnInfo(c net.Conn) (error) {
    addr := []byte(n.Addr)
    // Need space for ID, length of address (8 bytes), and the address
    msg := make([]byte, ID_SIZE + 8 + len(addr))
    copy(msg[:ID_SIZE], n.Id[:])
    binary.BigEndian.PutUint64(msg[ID_SIZE:], uint64(len(addr)))
    copy(msg[ID_SIZE+8:], addr)
    return writeExact(c, msg)
}


func getFirstDiffBit(a, b [ID_SIZE]byte) int {
    for i:=0; i < ID_SIZE; i++ {
        diff := a[i] ^ b[i]
        if diff != 0 {
            for j:=7; j >= 0; j-- {
                if ((diff >> j) & 1) != 0 {
                    return 8*i + 7 - j;
                }
            }
        }
    }
    return ID_SIZE * 8 - 1
}

// NOTE: Update on every request/response
func (n *Node) updateBuckets(otherId [ID_SIZE]byte, addr string) {
    n.BucketsLock.Lock()
    defer n.BucketsLock.Unlock()
    bucketIdx := getFirstDiffBit(n.Id, otherId)
    // Copy as slice so it is mutable
    bucket := n.Buckets[bucketIdx][:]
    bucketSize := n.BucketSizes[bucketIdx]

    seenIdx := -1
    for i:=0; i < bucketSize; i++ {
        if bucket[i].Id == otherId {
            seenIdx = i
            break
        }
    }

    if seenIdx == -1 && bucketSize < K {
        //n.Buckets[bucketIdx][bucketSize] = &BucketEntry{otherId, addr}
        bucket[bucketSize] = &BucketEntry{otherId, addr}
        n.BucketSizes[bucketIdx]++
    } else if seenIdx == -1 {
        // Ping least-recently-seen and move it to front if it responds, discarding otherId as it is newer
        lrsResponded := n.ping(bucket[0].Addr)

        if lrsResponded {
            temp := bucket[0]
            for i := 0; i < bucketSize-1; i++ {
                bucket[i] = bucket[i+1]
            }
            bucket[bucketSize-1] = temp
        } else {
            // Delete lrs and move entries back so there is space at front
            for i := 0; i < bucketSize-1; i++ {
                bucket[i] = bucket[i+1]
            }
            bucket[bucketSize-1] = &BucketEntry{otherId, addr}
        }
    } else if seenIdx != bucketSize - 1 {
        // Move otherId's bucket entry to the front of the bucket
        temp := bucket[seenIdx]
        for i:=seenIdx; i < bucketSize-1; i++ {
            bucket[i] = bucket[i+1]
        }
        bucket[bucketSize-1] = temp
    }
    // Ignore when otherId is already at the end of bucket

}


func (n *Node) ping(addr string) bool {

    log.Println("Pinging:", addr)
    c, err := net.Dial("tcp", addr)
    if err != nil {
        log.Println(err.Error())
        return false
    }

    n.writeOwnInfo(c)

    // generate random 160 bits
    buffer := [1+ID_SIZE]byte{}
    buffer[0] = REQ_PING
    _, err = rand.Read(buffer[1:])
    if err != nil {
        log.Println(err.Error())
    }
    // Send it to ping recipient
    _,err = c.Write(buffer[:])
    if err != nil {
        log.Println(err.Error())
        return false
    }
    // recipient echos back the random id bits or is dead
    buffer2 := [ID_SIZE]byte{}
    _, err = c.Read(buffer2[:])
    if err != nil {
        log.Println(err.Error())
        return false
    }

    // Ensure correct
    for i:=0; i < ID_SIZE; i++ {
        if buffer[i+1] != buffer2[i] {
            return false
        }
    }

    return true
}

func (n *Node) handlePing(c net.Conn) {
    buffer := [ID_SIZE]byte{}
    num, err := c.Read(buffer[:])
    if err != nil {
        log.Println(err.Error())
    }
    num, err = c.Write(buffer[:]);
    if err != nil {
        log.Println(err.Error())
    }

    if num != ID_SIZE {
        log.Println("Error not all bytes sent, only sent:", n)
    }
}


func (n *Node) store(content []byte) {
    id := sha1.Sum(content)
    closest := n.nodeLookup(id)

    c, err := net.Dial("tcp", closest.Addr)
    if err != nil {
        log.Println(err.Error())
    }

    n.writeOwnInfo(c)

    // Contains: req_type byte + msg_len + content bytes
    message := make([]byte, 1 + 8 + len(content))
    message[0] = REQ_STORE
    binary.BigEndian.PutUint64(message[1:9], uint64(len(content)))
    copy(message[9:], content)
    writeExact(c, message)
    // TODO: Handle error status returned
}

func (n *Node) handleStore(c net.Conn) {
    contentSizeBuff := [8]byte{}
    err := readExact(c, contentSizeBuff[:])
    if err != nil {
        log.Println(err.Error())
    }
    contentSize := binary.BigEndian.Uint64(contentSizeBuff[:])

    content := make([]byte, contentSize)
    err = readExact(c, content[:])
    if err != nil {
        log.Println(err.Error())
    }

    // TODO: Forward store maybe
    id := sha1.Sum(content)
    n.Storage[id] = content
    // TODO: Communicate error status back
}


func (n *Node) getClosest(other [ID_SIZE]byte, num int) []*BucketEntry {
    //TODO: If num < K sort bucket for closest
    closests := []*BucketEntry{}
    nClose := 0
    bucketIdx := getFirstDiffBit(n.Id, other)
    n.BucketsLock.RLock()
    defer n.BucketsLock.RUnlock()
    // Get all from this bucket and more general buckets until we have r closest known
    for i:=bucketIdx; i >= 0 &&  nClose < num; i-- {
        for j:=0; nClose < num && j < n.BucketSizes[i]; j++ {
            closests = append(closests, n.Buckets[i][j])
            nClose++
        }
    }

    // Get from more specific buckets (buckets closer to me vs other id) if r closest
    // still not found
    for i:=bucketIdx+1; i < len(n.Buckets) && nClose < num; i++ {
        for j:=0; nClose < num && j < n.BucketSizes[i]; j++ {
            closests = append(closests, n.Buckets[i][j])
            nClose++
        }
    }

    return closests
}


func (n *Node) nodeLookup(id [ID_SIZE]byte) BucketEntry {
    // Pick r closest nodes to id (i.e. from k-bucket of same or closest dist)

    closests := n.getClosest(id, N_LOOKUP)
    seen := make(map[[ID_SIZE]byte]bool)
    pq := make(PriorityQueue, len(closests))
    for i:=0; i < len(closests); i++ {
        pq[i] = &Item{
            entry: closests[i],
            priority: getFirstDiffBit(id, closests[i].Id),
            index: i,
        }
        seen[closests[i].Id] = true
    }
    heap.Init(&pq)
    // Most similar
    closestSeen := pq[0].entry
    closestSim := pq[0].priority

    // TODO: make concurrent (Note the N_LOOKUP (a.k.a 'a') controllers how many conc.
    // requests are made at a time and is therefore not used in non-concurrent version.
    for pq.Len() > 0 {
        //send find node to each
        next := pq.Pop().(*Item)
        if next.priority > closestSim {
            closestSeen = next.entry
            closestSim = next.priority
        }
        // recipient returns k closest nodes it knows about
        newNodes := n.findNode(next.entry.Addr, id)
        // Loop through new nodes adding any that haven't been seen to queue
        for i:=0; i < len(newNodes); i++ {
            newN := newNodes[i]
            _, exists := seen[newN.Id]
            if !exists {
                seen[newN.Id] = true
                heap.Push(&pq, &Item{
                    entry: &newN,
                    priority: getFirstDiffBit(newN.Id, id),
                })
            }
        }

        // Discard any more than K closest nodes
        // TODO: better system to keep K closest nodes
        if pq.Len() > K {
            keepNodes := [K]*Item{}
            for i:=0; i < K; i++ {
                keepNodes[i] = heap.Pop(&pq).(*Item)
            }
            pq = pq[:K]
            for i:=0; i < K; i++ {
                pq[i] = keepNodes[i]
            }
            heap.Init(&pq)
        }

    }
    return *closestSeen
}


func (n *Node) findNode(addr string, findId [ID_SIZE]byte) []BucketEntry {
    c, err := net.Dial("tcp", addr)
    if err != nil {
        log.Println(err.Error())
    }

    n.writeOwnInfo(c)

    buffer := [ID_SIZE + 1]byte{}
    buffer[0] = REQ_FIND_NODE
    copy(buffer[1:], findId[:])
    err = writeExact(c, buffer[:])
    if err != nil {
        log.Println(err.Error())
        return nil
    }

    numEntryBuffer := [8]byte{}
    err = readExact(c, numEntryBuffer[:])
    if err != nil {
        log.Println(err.Error())
    }
    nEntries := int(binary.BigEndian.Uint64(numEntryBuffer[:]))

    addrSizesBuffer := make([]byte, 8 * nEntries)
    err = readExact(c, addrSizesBuffer[:])
    addrSizes := make([]int, nEntries)
    totalAddrSize := 0
    for i:=0; i < nEntries; i++ {
        addrSizes[i] = int(binary.BigEndian.Uint64(addrSizesBuffer[8*i:]))
        totalAddrSize += addrSizes[i]
    }

    res := make([]BucketEntry, nEntries)
    dataBuffer := make([]byte, ID_SIZE * nEntries + totalAddrSize)
    err = readExact(c, dataBuffer)
    if err != nil {
        log.Println(err.Error())
    }


    ids := dataBuffer[:ID_SIZE*nEntries]
    for i:=0; i < nEntries; i++ {
        copy(res[i].Id[:], ids[ID_SIZE*i:ID_SIZE*(i+1)])
    }

    addrs := dataBuffer[ID_SIZE * nEntries:]
    addrStart := 0
    for i :=0; i < nEntries; i++ {
        res[i].Addr = string(addrs[addrStart:addrStart +  int(addrSizes[i])])
        addrStart += int(addrSizes[i])
    }

    return res
}

func (n *Node) handleFindNode(c net.Conn) {
    id := [ID_SIZE]byte{}
    err := readExact(c, id[:])
    if err != nil {
        log.Println(err)
    }

    closests := n.getClosest(id, K)
    nClose := len(closests)

    //Format and return results to caller
    // Format: num neighbors returning (8 byte) 
    //         + n * id (32) + addr len (8) + addr
    message := make([]byte, 8)
    binary.BigEndian.PutUint64(message, uint64(nClose))
    sizes := make([]byte, 8 * nClose)
    ids := make([]byte, ID_SIZE * nClose)
    addrs := []byte{}
    for i:=0; i < nClose; i++ {
        addr := closests[i].Addr
        copy(ids[ID_SIZE*i:], closests[i].Id[:])
        binary.BigEndian.PutUint64(sizes[8*i:], uint64(len(addr)))
        addrs = append(addrs, []byte(addr)...)
    }

    message = append(message, sizes...)
    message = append(message, ids...)
    message = append(message, addrs...)

    err = writeExact(c, message)
    if err != nil {
        log.Println(err.Error())
    }
}


func (n *Node) findValue() {
    // Same as findNode but with early exit on finding the value and caching
}


func (n *Node) handleRequest(c net.Conn) {
    log.Println("Request from: " + c.RemoteAddr().String())
    defer c.Close()

    reqId := [ID_SIZE]byte{}
    err := readExact(c, reqId[:])
    if err != nil {
        log.Println(err.Error)
    }
    // Note this is not for the address of the connection but the address that the
    // other node is sending a request from
    reqAddrBytes := [8]byte{}
    err = readExact(c, reqAddrBytes[:])
    if err != nil {
        log.Println(err.Error)
    }
    reqAddrSize := binary.BigEndian.Uint64(reqAddrBytes[:])
    reqAddr := make([]byte, reqAddrSize)
    err = readExact(c, reqAddr)
    if err != nil {
        log.Println(err.Error)
    }

    // Add request sender to K buckets
    n.updateBuckets(reqId, string(reqAddr))

    var reqType [1]byte

    num,err := c.Read(reqType[:]);
    if err != nil {
        log.Println(err.Error())
    }

    if num == 0 {
        log.Println("ERROR: No byte read!")
    }

    switch reqType[0] {
        case REQ_PING:
            n.handlePing(c)
            break
        case REQ_STORE:
            n.handleStore(c)
            break
        case REQ_FIND_NODE:
            n.handleFindNode(c)
            break
        case REQ_FIND_VAL:
            log.Println("Find value!")
            break
        default:
            log.Println("ERROR: Request type not recognized:", reqType)
    }

    log.Println("Finished request from: " + c.RemoteAddr().String())
}


func (n *Node) runNode(addr string, known []*BucketEntry) {
    if addr != "" {
        n.Addr = addr
        n.Id = sha1.Sum([]byte(addr))

        ln, err := net.Listen("tcp", addr)
        if err != nil {
            log.Fatal(err)
        }
        defer ln.Close()

        log.Println("Listenting at ", addr)
        for {
            conn, err := ln.Accept()
            if err != nil {
                log.Println(err.Error())
            }
            go n.handleRequest(conn)
        }
    } else {
        ln, err := net.Listen("tcp", "127.0.0.1:0")
        if err != nil {
            log.Fatal(err)
        }
        defer ln.Close()

        n.Addr = ln.Addr().String()
        n.Id = sha1.Sum([]byte(n.Addr))

        for i:=0; i < len(known); i++ {
            bucketIdx := getFirstDiffBit(n.Id, known[i].Id)
            size := n.BucketSizes[bucketIdx]
            if size < 20 {
                if (n.ping(known[i].Addr)) {
                    n.Buckets[bucketIdx][size] = known[i]
                    n.BucketSizes[bucketIdx]++
                }
            }
        }

        log.Println("Listenting at", ln.Addr())
        for {
            conn, err := ln.Accept()
            if err != nil {
                log.Println(err.Error())
            }
            go n.handleRequest(conn)
        }
    }
}


func main() {

    if len(os.Args) == 1 {
        var node Node
        node.Addr = "127.0.0.1:6969"
        node.Id = sha1.Sum([]byte(node.Addr))

        for i:=0; i < 50; i++ {
            addr := "127.0.0.1:" + strconv.Itoa(5970+i)
            id := sha1.Sum([]byte(addr))
            node.updateBuckets(id, addr)
            log.Println(node.BucketSizes)
        }

        ln, err := net.Listen("tcp", ":6969")
        if err != nil {
            log.Fatal(err)
        }

        log.Println("Listening on port:", "6969")
        for {
            conn, err := ln.Accept()
            if err != nil {
                log.Println(err.Error())
            }

            go node.handleRequest(conn)
        }
    } else if os.Args[1] == "test" {
        //var node Node
        //node.Addr = "127.0.0.1:6969"
        //node.Id = sha1.Sum([]byte(node.Addr))

        //for i:=0; i < 50; i++ {
        //    addr := "127.0.0.1:" + strconv.Itoa(5970+i)
        //    id := sha1.Sum([]byte(addr))
        //    node.updateBuckets(id, addr)
        //    log.Println(node.BucketSizes)
        //}

        //toLook := sha1.Sum([]byte("127.0.0.1:420"))
        //log.Println("Id:", toLook);
        //node.nodeLookup(toLook)

        pq := make(PriorityQueue, 20)
        for i:=0; i < 20; i++ {
            pq[i] = &Item{
                entry:&BucketEntry{},
                priority: i,
                index: i,
            }
        }
        heap.Init(&pq)

        //for pq.Len() > 0 {
        //    log.Println(heap.Pop(&pq).(*Item).priority)
        //}
        //log.Println()

        for i:=0; i < 100; i++ {
            heap.Push(&pq, &Item{
                entry: &BucketEntry{},
                priority: i,
            })
        }

        for pq.Len() > 0 {
            log.Println(heap.Pop(&pq).(*Item).priority)
        }
    } else if os.Args[1] == "n" {
        numNodes, err := strconv.Atoi(os.Args[2])
        if err != nil {
            log.Fatal(err)
        }

        nodes := make([]Node, numNodes)

        rootAddr := "127.0.0.1:6969"

        go (&nodes[0]).runNode(rootAddr, []*BucketEntry{})

        time.Sleep(2 * time.Second)

        known := []*BucketEntry{ &BucketEntry{sha1.Sum([]byte(rootAddr)), rootAddr} }
        for i:=1; i < numNodes; i++ {
            go (&nodes[i]).runNode("", known)
        }

        time.Sleep(2 * time.Second);

        for {}
    }
}












