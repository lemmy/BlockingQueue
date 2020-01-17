package main

import (
	"fmt"
	"sync"
)

type BlockingQueue struct {
	lock *sync.Mutex

	cond *sync.Cond

	size int

	head int

	tail int

	store []interface{}
}

func NewBlockingQueue(capacity int) *BlockingQueue {
	lock := new(sync.Mutex)

	return &BlockingQueue{
		lock:  lock,
		cond:  sync.NewCond(lock),
		size:  int(0),
		store: make([]interface{}, capacity),
	}
}

func (q *BlockingQueue) Take() interface{} {
	q.lock.Lock()

	for q.size == 0 {
		q.cond.Wait()
	}

	// head
	var item = q.store[q.head]
	q.store[q.head] = nil
	q.tail = (q.tail + 1) % len(q.store)
	q.size = q.size - 1

	q.cond.Signal()
	q.lock.Unlock()

	return item
}

func (q *BlockingQueue) Put(item interface{}) {
	q.lock.Lock()

	for q.size == len(q.store) {
		q.cond.Wait()
	}

	// append
	q.store[q.tail] = item
	q.tail = (q.tail + 1) % len(q.store)
	q.size = q.size + 1

	q.cond.Signal()
	q.lock.Unlock()
}

// ***********************************************

// go build BlockingQueue.go
// go run BlockingQueue.go
// go run -race BlockingQueue.go

func main() {

	fmt.Println("Hello blocking queue")

	var q = NewBlockingQueue(3)

	// Prevent main from terminating before Producers
	// and Consumers are done (or deadlocked).
	wg := sync.WaitGroup{}

	for producer := 0; producer < 4; producer++ {
		wg.Add(1)
		go func(wg *sync.WaitGroup) {
			for i := 0; i < 1000; i++ {
				q.Put(i)
			}
			wg.Done()
		}(&wg)
	}

	for consumer := 0; consumer < 3; consumer++ {
		wg.Add(1)
		go func(wg *sync.WaitGroup) {
			for i := 0; i < 1000; i++ {
				q.Take()
				if i%10000 == 0 {
					fmt.Println("consumed", i)
				}
			}
			wg.Done()
		}(&wg)
	}

	wg.Wait()

	fmt.Println("Done blocking queue")
}
