
// Implementation kindly provided by Aman Jain (https://www.linkedin.com/in/aman-jain-334a49110/).

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <pthread.h>

uint32_t buff_size, numProducers, numConsumers;
uint32_t *buffer;
uint32_t fillIndex, useIndex, count = 0;

// See https://stackoverflow.com/a/2087046/6291195 to relate this to the Java impl.
pthread_cond_t empty, full; 
pthread_mutex_t mutex;

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

void *producer (void * arg) {
	while(1) {
		pthread_mutex_lock(&mutex);   // acquire the lock	
		while (count == buff_size) {   // check if the buffer is full
			#ifdef TRACE
			printf("w#p#-1\n");	fflush(stdout);
			#endif

		    pthread_cond_wait(&empty, &mutex);
		}
		
		append(rand() % (10));        // produce!
		#ifdef TRACE
		printf("e#p#-1\n"); fflush(stdout);
		#endif

		pthread_cond_signal(&full); // broadcast that the buffer is full
        pthread_mutex_unlock(&mutex); // release the lock
	}
}

void *consumer (void * arg) {
	uint32_t id = *((uint32_t *) arg);
	long report = 0;
	while(1) {
		pthread_mutex_lock(&mutex);   // acquire the lock

		while (count == 0) {           // check if the buffer is empty
			#ifdef TRACE
			printf("w#c#%d\n", id); fflush(stdout);
			#endif

			pthread_cond_wait(&full, &mutex); // wait for the buffer to be filled
		}

		head();                       // consume (we don't care about the value)!
		#ifdef TRACE
		printf("d#c#%d\n", id);  fflush(stdout);
		#endif
		
		pthread_cond_signal(&empty); // signal that the buffer is empty
		pthread_mutex_unlock(&mutex); // release the lock
		
		#ifndef TRACE 
		if (report++ % 10000 == 0) {
    		printf("\n%ld values consumed by %d", report, id);
		}
		#endif
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

	#ifndef TRACE 
	printf("Buffer size = %d, # Producers = %d, # Consumers = %d\n", buff_size, numProducers, numConsumers);
	#endif

	pthread_mutex_init(&mutex, NULL);
	pthread_cond_init(&empty, NULL);
	pthread_cond_init(&full, NULL);

	/* Allocate space for the buffer */
	buffer = malloc(sizeof(int) * buff_size);
	pthread_t prods[numProducers], cons[numConsumers];
	uint32_t threadIds[numConsumers];

	uint32_t i;
	/* Create the producer */
	for (i = 0; i < numProducers ; i++) {
		pthread_create(&prods[i], NULL, producer, NULL);
	}

	/* Create the consumers */
	for (i = 0; i < numConsumers; i++) {
		threadIds[i] = i;
		pthread_create(&cons[i], NULL, consumer, &threadIds[i]);
	}

	/* Wait for all threads to finish */
	for (i = 0; i < numProducers ; i++) 
		pthread_join(prods[i], NULL);	

	for (i = 0; i < numConsumers; i++)
		pthread_join(cons[i], NULL);

	return 0;
}
