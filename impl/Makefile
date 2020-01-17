all: producer_consumer

producer_consumer: producer_consumer.c
	gcc producer_consumer.c -o producer_consumer -pthread

arm64: producer_consumer.c
	gcc -target arm64-apple-macos11 producer_consumer.c -o producer_consumer -pthread

cocoa: producer_consumer_cocoa.m
	clang -framework Foundation producer_consumer_cocoa.m -o producer_consumer

clean:
	rm producer_consumer
