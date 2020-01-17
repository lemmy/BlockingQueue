all: producer_consumer

trace: producer_consumer.c
	gcc -DNDEBUG -DTRACE producer_consumer.c -o producer_consumer -pthread

producer_consumer: producer_consumer.c
	gcc -DNDEBUG producer_consumer.c -o producer_consumer -pthread

arm64: producer_consumer.c
	gcc -DNDEBUG -target arm64-apple-macos11 producer_consumer.c -o producer_consumer -pthread

cocoa: producer_consumer_cocoa.m
	clang -framework Foundation producer_consumer_cocoa.m -o producer_consumer

clean:
	rm producer_consumer
