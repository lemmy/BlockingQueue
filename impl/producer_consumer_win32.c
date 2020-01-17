
#include <windows.h>
#include <stdio.h>
#include <stdint.h>

uint32_t buff_size, numProducers, numConsumers;
uint32_t *buffer;
uint32_t fillIndex, useIndex, count = 0;

CRITICAL_SECTION mutex;
CONDITION_VARIABLE modify;

void append(uint32_t value) {
	buffer[fillIndex] = value;
	fillIndex = (fillIndex + 1) % buff_size;
	count++;
}

uint32_t head() {
	uint32_t tmp = buffer[useIndex];
	useIndex = (useIndex + 1) % buff_size;
	count--;
	return tmp;
}

DWORD WINAPI producer(LPVOID lpParam) {
	while(1) {
		EnterCriticalSection(&mutex);   // acquire the lock	
		while (count == buff_size)    // check if the buffer is full
		    SleepConditionVariableCS(&modify, &mutex, INFINITE);
		
		append(rand() % (10));        // produce!

		WakeConditionVariable(&modify); // broadcast that the buffer is full
        LeaveCriticalSection(&mutex); // release the lock
	}
}

DWORD WINAPI consumer(LPVOID lpParam) {
	long report = 0;
	while(1) {
		EnterCriticalSection(&mutex);   // acquire the lock

		while (count == 0)            // check if the buffer is empty
			SleepConditionVariableCS(&modify, &mutex, INFINITE); // wait for the buffer to be filled

		head();                       // consume (we don't care about the value)!
		WakeConditionVariable(&modify); // signal that the buffer is empty
		LeaveCriticalSection(&mutex); // release the lock
		
		if (report++ % 10000 == 0) {
    		printf("\n%ld values consumed", report);
		}
	} 
}

int main(int argc, char * argv[]) {
	if (argc < 4) {
		printf ("Usage: ./producer_consumer <buffer_size> <#_of_producers> <#_of_consumers> \n");
		exit(1);
	}

	srand(999);

	/* Process arguments */
	buff_size = atoi(argv[1]);
	numProducers = atoi(argv[2]);
	numConsumers = atoi(argv[3]);
	HANDLE *producers = malloc(sizeof(HANDLE) * numProducers);
	HANDLE *consumers = malloc(sizeof(HANDLE) * numConsumers);

	printf("Buffer size = %d, # Producers = %d, # Consumers = %d\n", buff_size, numProducers, numConsumers);

	InitializeCriticalSection(&mutex);
	InitializeConditionVariable(&modify);

	/* Allocate space for the buffer */
	buffer = malloc(sizeof(int) * buff_size);

	uint32_t i;
	/* Create the producer */
	for (i = 0; i < numProducers ; i++) {
		producers[i] = CreateThread(NULL, 0, producer, 0, 0, NULL);
	}

	/* Create the consumers */
	for (i = 0; i < numConsumers; i++)
		consumers[i] = CreateThread(NULL, 0, consumer, 0, 0, NULL);

	// Wait until all threads have terminated.
	WaitForMultipleObjects(numProducers, producers, TRUE, INFINITE);
	WaitForMultipleObjects(numConsumers, consumers, TRUE, INFINITE);

	/* Wait for all threads to finish */
	for (i = 0; i < numProducers ; i++) 
		CloseHandle(producers[i]);	

	for (i = 0; i < numConsumers; i++)
		CloseHandle(consumers[i]);

	DeleteCriticalSection(&mutex);
}
