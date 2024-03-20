package main

import (
    "encoding/binary"
    "errors"
    _ "encoding/hex"
    "container/heap"
    "flag"
    "log"
    "net"
    _ "os"
    "crypto/rand"
    "crypto/sha1"
    "sort"
    "strconv"
    "sync"
    "time"
)

const (
    REQ_PING byte =  iota
    REQ_STORE
    REQ_FIND_NODE
    REQ_FIND_VAL
)

const (
    VALUE_NOT_FOUND byte = iota
    VALUE_FOUND
)

// Size in bytes of ID. Currently 20 for 160 bit sha1 hash
const ID_SIZE = 20
// Size of the "k-buckets" i.e. the number of nodes stored for each distance from self
const K = 20
// Maximum number of parallel lookup requests to send at a time
const N_LOOKUP = 3

// Time between random node lookups for discovery purposes
const DISCOVERY_PERIOD = 1 * time.Second
// Maximum number of discovered nodes to add to K buckets
const MAX_DISCOVERY_NODES = K



// Entry in K buckets
type BucketEntry struct {
    Id [ID_SIZE]byte
    Addr string
}

/* Priority Queue for k bucket entries*/
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

// A node in the kademelia network
type Node struct{
    Addr string
    Id [ID_SIZE]byte
    // Need (with very low probability) a bucket for each bit where keys start to differ
    // 8 * ID_SIZE (in bytes) = id size in bits
    Buckets [ID_SIZE*8][K]*BucketEntry
    // Number of entries in each bucket
    BucketSizes [ID_SIZE*8]int
    // Everything stays in memory for simplicity
    Storage map[[ID_SIZE]byte][]byte
    BucketsLock sync.RWMutex
}



/*
 * Reads enough bytes from the connection to fill the given byte slice or returns 
 * an error.
 */
func readExact(c net.Conn, res []byte) (error) {
    n, err := c.Read(res)

    if n != len(res) {
        return errors.New("Number read does not match expected: " + strconv.Itoa(n) + " read vs. " + strconv.Itoa(len(res)) + " expected.")
    }
    return err
}


/*
 * Writes all of the data in the given slice or returns an error.
 */
func writeExact(c net.Conn, toWrite []byte) (error) {
    n, err := c.Write(toWrite)
    if n != len(toWrite) {
        return errors.New("Number written does not match expected: " + strconv.Itoa(n) + " written vs. " + strconv.Itoa(len(toWrite)) + " expected.")
    }
    return err
}


/*
 * Writes own ID and Address on the connection
 */
func (n *Node) writeOwnInfo(c net.Conn) (error) {
    addr := []byte(n.Addr)
    // Need space for ID, length of address (8 bytes), and the address
    msg := make([]byte, ID_SIZE + 8 + len(addr))
    copy(msg[:ID_SIZE], n.Id[:])
    binary.BigEndian.PutUint64(msg[ID_SIZE:], uint64(len(addr)))
    copy(msg[ID_SIZE+8:], addr)
    return writeExact(c, msg)
}


/*
 *  Get the index of the most significant bit where the two id's a and b differ.
 */
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

/*
 *  Returns true if a is close to tarId than b. False otherwise.
 */
func idLessDiff(tarId, a, b [ID_SIZE]byte) bool {
    for i:=0; i < ID_SIZE; i++ {
        diffA := tarId[i] ^ a[i]
        diffB := tarId[i] ^ b[i]
        if diffA < diffB {
            return true
        } else if diffA > diffB {
            return false
        }
    }
    return false

}

/*
 * Adds (otherId, addr) to the appropriate k bucket if there is room and checking 
 * for dead nodes to replace if there isn't. If there is no room the entry is not added
 */
func (n *Node) updateBuckets(otherId [ID_SIZE]byte, addr string) {
    if otherId == n.Id {
        return
    }
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


/*
 * Ping the node at the given address and ask them to echo a random 160 bits. Returns
 * true if they echo it without error. False otherwise.
 */
func (n *Node) ping(addr string) bool {

    log.Println("Pinging:", addr)
    c, err := net.Dial("tcp", addr)
    if err != nil {
        log.Println(err.Error())
        return false
    }
    defer c.Close()

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


/*
 * Handles a ping request to this node from the connected node.
 */
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


/*
 * Generates an id (hash) for the given content, finds a suitable node on the network,
 * and requests to store the content at that address.
 */
func (n *Node) store(content []byte) {
    id := sha1.Sum(content)
    closest := n.nodeLookup(id)

    c, err := net.Dial("tcp", closest.Addr)
    if err != nil {
        log.Println(err.Error())
    }
    defer c.Close()

    n.writeOwnInfo(c)

    // Contains: req_type byte + msg_len + content bytes
    message := make([]byte, 1 + 8 + len(content))
    message[0] = REQ_STORE
    binary.BigEndian.PutUint64(message[1:9], uint64(len(content)))
    copy(message[9:], content)
    writeExact(c, message)
    // TODO: Handle error status returned
}


/*
 * Handles a store request sent to this node from the connection c
 */
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

    id := sha1.Sum(content)
    n.Storage[id] = content
    // TODO: Send error status back
}


/*
 * Searches k buckets for the entry with the id closest to tarId
 */
func (n *Node) getClosest(tarId [ID_SIZE]byte, num int) []*BucketEntry {
    closests := []*BucketEntry{}
    nClose := 0
    bucketIdx := getFirstDiffBit(n.Id, tarId)
    n.BucketsLock.RLock()
    defer n.BucketsLock.RUnlock()
    // Get all from this bucket and more general buckets until we have at least r closest known
    for i:=bucketIdx; i >= 0 && nClose < num; i-- {
        // Don't exit early but store all in last closest bucket (so we can sort them later)
        for j:=0; j < n.BucketSizes[i]; j++ {
            closests = append(closests, n.Buckets[i][j])
            nClose++
        }
    }

    // Get from more specific buckets (buckets closer to me vs tarId id) if r closest
    // still not found
    for i:=bucketIdx+1; i < len(n.Buckets) && nClose < num; i++ {
        for j:=0; nClose < num && j < n.BucketSizes[i]; j++ {
            closests = append(closests, n.Buckets[i][j])
            nClose++
        }
    }

    // Sort closests according to which Id is most similar to the target
    sort.Slice(closests, func(i, j int) bool {
        return idLessDiff(tarId, closests[i].Id, closests[j].Id)
    })

    if num < nClose {
        return closests[:num]
    }
    return closests

}


/*
 * Search connected nodes for the closest node to the given id. Returns a bucket entry
 * (id, address) for the closest node.
 */
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


func (n *Node) findHelper(c net.Conn) []BucketEntry {
    numEntryBuffer := [8]byte{}
    err := readExact(c, numEntryBuffer[:])
    if err != nil {
        log.Println(err.Error())
    }
    // Number of nodes/bucket entries returned
    nEntries := int(binary.BigEndian.Uint64(numEntryBuffer[:]))

    // Sizes of each bucket entry's address
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



/*
 * Since handleFindNode and handleFindValue do the same thing when the value is not 
 * found this method does that core chunk of the find process, namely, finds the k 
 * closest k bucket entries and returns them (or all entries if there are less than k)
 */
func (n *Node) handleFindHelper(c net.Conn, id [ID_SIZE]byte) {
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

    err := writeExact(c, message)
    if err != nil {
        log.Println(err.Error())
    }
}


/*
 * Sends a request to the given address asking for it's K closest neighbors. These
 * or however many neighbors the node has are returned.
 */
func (n *Node) findNode(addr string, findId [ID_SIZE]byte) []BucketEntry {
    c, err := net.Dial("tcp", addr)
    if err != nil {
        log.Println(err.Error())
    }
    defer c.Close()

    n.writeOwnInfo(c)

    buffer := [ID_SIZE + 1]byte{}
    buffer[0] = REQ_FIND_NODE
    copy(buffer[1:], findId[:])
    err = writeExact(c, buffer[:])
    if err != nil {
        log.Println(err.Error())
        return nil
    }

    return n.findHelper(c)
}


/*
 * Handle a findNode request from the connected node. Finds the closest node in own
 * k buckets to the target id sent from the connected node and responds with them.
 */
func (n *Node) handleFindNode(c net.Conn) {
    id := [ID_SIZE]byte{}
    err := readExact(c, id[:])
    if err != nil {
        log.Println(err)
    }

    n.handleFindHelper(c, id)

}


/*
 * Sends request to a given address looking for a value stored under the given findId. 
 * If found, the value is returned. Otherwise the closest nodes the other node knows
 * are returned.
 */
func (n *Node) findValue(addr string, findId [ID_SIZE]byte) (value []byte, closests []BucketEntry, wasFound bool) {
    c, err := net.Dial("tcp", addr)
    if err != nil {
        log.Println(err.Error())
    }
    defer c.Close()

    n.writeOwnInfo(c)

    buffer := [ID_SIZE + 1]byte{}
    buffer[0] = REQ_FIND_NODE
    copy(buffer[1:], findId[:])
    err = writeExact(c, buffer[:])
    if err != nil {
        log.Println(err.Error())
        return []byte{}, []BucketEntry{}, false
    }


    wasFoundBuffer := [1]byte{}
    err = readExact(c, wasFoundBuffer[:])
    if err != nil {
        log.Println(err.Error())
    }

    wasFound = wasFoundBuffer[0] == VALUE_FOUND
    if wasFound {
        closests = []BucketEntry{}

        lenBuffer := [8]byte{}
        err = readExact(c, lenBuffer[:])
        if err != nil {
            log.Println(err.Error())
            return []byte{}, []BucketEntry{}, false
        }

        value := make([]byte, binary.BigEndian.Uint64(lenBuffer[:]))
        readExact(c, value)

    } else {
        value = []byte{}
        closests = n.findHelper(c)
    }

    return
}

func (n *Node) handleFindValue(c net.Conn) {
    // TODO: caching
    id := [ID_SIZE]byte{}
    err := readExact(c, id[:])
    if err != nil {
        log.Println(err)
    }

    value, exists := n.Storage[id]
    if exists {
        // Send the value
        buffer := make([]byte, 1 + 8 + len(value))
        buffer[0] = VALUE_FOUND
        binary.BigEndian.PutUint64(buffer[1:9], uint64(len(value)))
        copy(buffer[9:], value)
        writeExact(c, buffer[:])
    } else {
        // Send the k closest nodes this node konws about
        buffer := [1]byte{}
        buffer[0] = VALUE_NOT_FOUND
        writeExact(c, buffer[:])
        n.handleFindHelper(c, id)
    }
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
        log.Println(n.Addr)

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

        // Add known addresses to K buckets
        for i:=0; i < len(known); i++ {
            bucketIdx := getFirstDiffBit(n.Id, known[i].Id)
            size := n.BucketSizes[bucketIdx]
            if size < 20 {
                if (n.ping(known[i].Addr)) {
                    func(){
                        n.BucketsLock.Lock()
                        defer n.BucketsLock.Unlock()
                        n.Buckets[bucketIdx][size] = known[i]
                        n.BucketSizes[bucketIdx]++
                    }()
                }
            }
        }

        // Startup node discovery routine
        go n.runNodeDiscoveryRoutine()

        // Serve requests
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


func (n *Node) runNodeDiscoveryRoutine() {
    for {
        time.Sleep(DISCOVERY_PERIOD)
        randId := [ID_SIZE]byte{}
        _, err := rand.Read(randId[:])
        if err != nil {
            log.Println(err.Error())
            continue
        }

        closestList := n.getClosest(randId, 1)
        if len(closestList) == 0 {
            continue
        }

        newNodes := n.findNode(closestList[0].Addr, randId)

        for i:=0; i < len(newNodes) && i < MAX_DISCOVERY_NODES; i++ {
            n.updateBuckets(newNodes[i].Id, newNodes[i].Addr);
        }


    }
}


func main() {


    knownPtr := flag.String("known", "", "Known address to connect to. If blank this node starts it's own network.")
    hostPtr := flag.String("host", "127.0.0.1", "Ip address to host this node on.")
    portPtr := flag.Int("port", 6969, "Port to host this node on.")

    numExtraPtr := flag.Int("extra", 0, "Number of extra nodes to start and connect.")
    startupDelayPtr := flag.Int("delay", 2000, "Milliseconds to wait after starting first node before starting the rest when starting a network.")

    flag.Parse()

    nodes := make([]Node,*numExtraPtr+1)
    if *knownPtr == "" {
        rootAddr := *hostPtr + ":" + strconv.Itoa(*portPtr)
        go (&nodes[0]).runNode(rootAddr, []*BucketEntry{})

        time.Sleep(time.Duration(*startupDelayPtr) * time.Millisecond)

        known := []*BucketEntry{ &BucketEntry{sha1.Sum([]byte(rootAddr)), rootAddr} }
        for i:=1; i < len(nodes); i++ {
            go (&nodes[i]).runNode("", known)
        }
    } else {
        known := []*BucketEntry{ &BucketEntry{sha1.Sum([]byte(*knownPtr)), *knownPtr} }
        for i:=0; i < len(nodes); i++ {
            go (&nodes[i]).runNode("", known)
        }
    }

    /*Run until interrupt*/
    for {}
}












