#import <Foundation/Foundation.h>

int main(int argc, const char * argv[]) {
    @autoreleasepool {
        if (argc < 4) {
            printf ("Usage: ./producer_consumer <buffer_size> <#_of_producers> <#_of_consumers> \n");
            exit(1);
        }

        /* Process arguments */
        const int buff_size = atoi(argv[1]);
        const int numProducers = atoi(argv[2]);
        const int numConsumers = atoi(argv[3]);

        printf("Buffer size = %d, # Producers = %d, # Consumers = %d\n", buff_size, numProducers, numConsumers);
        
        // This lock just keeps the main thread from terminating
        // but has nothing to do with the deadlock we want to
        // study.
        NSLock *waitForever = [NSLock new];

        // This is the interesting lock (https://developer.apple.com/documentation/foundation/nscondition)
        NSCondition *lock = [NSCondition new];
        
        // Simplified queue to a simple counter.
        __block int count = 0;
    
        for (int i = 0; i < numProducers; i++) {
            [NSThread detachNewThreadWithBlock:^{
                while (YES) {
                    [lock lock];
                    while (count == buff_size) {
                        [lock wait];
                    }
                    count = count + 1;
                    // Replace signal with broadcast here and
                    // below to workaround the deadlock.
                    [lock signal];
                    [lock unlock];
                }
            }];
        }

        for (int i = 0; i < numConsumers; i++) {
            [NSThread detachNewThreadWithBlock:^{
                long report = 0;
                while (YES) {
                    [lock lock];
                    while (count == 0) {
                        [lock wait];
                    }
                    count = count - 1;
                    [lock signal];
                    [lock unlock];
                    if (report++ % 10000 == 0) {
                        printf("\n%ld values consumed by %d", report, i);
                    }
                }
            }];
        }

        [waitForever lock];
        [waitForever lock]; // wait forever until users kills the process.
    }
    return 0;
}
