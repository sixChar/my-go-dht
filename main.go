package main

import (
    "errors"
    "encoding/binary"
    "log"
    "net"
    "crypto/rand"
    "crypto/sha1"
    "strconv"
    _ "os"
)

const (
    REQ_PING byte =  iota
    REQ_STORE
    REQ_FIND_NODE
    REQ_FIND_VAL
)

const ID_SIZE = 20
const K = 20

type BucketEntry struct {
    Id [ID_SIZE]byte
    Addr string
}

type Node struct{
    Addr string
    Id [ID_SIZE]byte
    Buckets [ID_SIZE][K]*BucketEntry
    BucketSizes [ID_SIZE]int
}


func readExact(c net.Conn, res []byte) (error) {
    nRead, err := c.Read(res)

    if nRead != len(res) {
        return errors.New("Number read does not match expected:" + strconv.Itoa(nRead) + "read vs. " + strconv.Itoa(len(res)) + "expected.")
    }
    return err
}


func writeExact(c net.Conn, toWrite []byte) (error) {
    n, err := c.Write(toWrite)
    if n != len(toWrite) {
        return errors.New("Number written does not match expected:" + strconv.Itoa(nRead) + "written vs. " + strconv.Itoa(len(res)) + "expected.")
    }
    return err
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
        // TODO: Ping least-recently-seen and move it to front if it responds, discarding otherId as it is newer
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

    c, err := net.Dial("tcp", addr)
    if err != nil {
        log.Println(err.Error())
        return false
    }

    // generate random 160 bits
    buffer := [1+ID_SIZE]byte{}
    buffer[0] = REQ_PING
    _, err = rand.Read(buffer[1:])
    if err != nil {
        log.Println(err.Error())
    }
    log.Println("Sent: ", buffer)
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
    log.Println("Received: ", buffer2)

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
    closest := n.findeNode(id)

    c, err := net.Dial(closest.Addr)
    if err != nil {
        log.Println(err.Error())
    }

    // Contains: req_type byte + msg_len + content bytes
    message = make([]byte, 1 + 8 + len(content))
    message[0] = REQ_STORE
    binary.BigEndian.PutUint64(message[1:9], len(content))
    message[9:] = content
    writeExact(c, message)
    // TODO: Handle error status returned
}

func (n *Node) handleStore(c net.Conn) {
    contentSizeBuff := [8]byte{}
    err = readExact(c, contentSizeBuff[:])
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
    n.storage[id] = content
    // TODO: Communicate error status back
}

func (n *Node) nodeLookup(id [ID_SIZE]byte) {
    // Pick r closest nodes to id (i.e. from k-bucket of same or closest dist)
    // Send find_node to each
    // recipient returns k closest nodes it knows about
    // Send find_nodes to next r closest seen
    // Repeat until query and responses from k closest nodes with no new closer nodes.
}


func (n *Node) handleFindNode(c net.Conn) {
    id := [ID_SIZE]byte{}
    readExact(c, id[:])
    
}


func (n *Node) findValue() {
    // Same as findNode but with early exit on finding the value and caching
}


func (n *Node) handleRequest(c net.Conn) {
    defer c.Close()
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
            log.Println("Store!")
            break
        case REQ_FIND_NODE:
            log.Println("Find node!")
            break
        case REQ_FIND_VAL:
            log.Println("Find value!")
            break
        default:
            log.Println("ERROR: Request type not recognized:", reqType)

    }

}


func main() {
    //if len(os.Args) == 1 {

    //    ln, err := net.Listen("tcp", ":6969")
    //    if err != nil {
    //        log.Fatal(err)
    //    }

    //    log.Println("Listening on port:", "6969")
    //    for {
    //        conn, err := ln.Accept()
    //        if err != nil {
    //            log.Println(err.Error())
    //        }

    //        go n.handleRequest(conn)
    //    }
    //} else {
    //    n := Node{}
    //    log.Println(n.ping("127.0.0.1:6969"));
    //}

    var node Node
    node.Addr = "127.0.0.1:6969"
    node.Id = sha1.Sum([]byte(node.Addr))

    for i:=0; i < 500; i++ {
        addr := "127.0.0.1:" + strconv.Itoa(6970+i)
        id := sha1.Sum([]byte(addr))
        node.updateBuckets(id, addr)
        log.Println(node.BucketSizes)
    }

}












