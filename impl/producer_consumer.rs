use std::env;
use std::thread;
use std::sync::{Arc, Condvar, Mutex};

fn main() {
    let args: Vec<String> = env::args().collect();

    let buffer_size = args.get(1).unwrap_or(&String::from("3")).parse::<usize>().unwrap();
    let num_producers = args.get(2).unwrap_or(&String::from("4")).parse::<usize>().unwrap();
    let num_consumers = args.get(3).unwrap_or(&String::from("3")).parse::<usize>().unwrap();

    let buffer = Arc::new((Mutex::new(Vec::with_capacity(buffer_size)), Condvar::new()));
	println!("Buffer size = {}, # Producers = {}, # Consumers = {}", buffer_size, num_producers, num_consumers);

    let producers: Vec<_> = (0..num_producers).map(|i| {
        let buffer = Arc::clone(&buffer);
        thread::spawn(move || {
            loop {
                let item = format!("Producer {}: Item {}", i, i);

                let (lock, cvar) = &*buffer;
                let mut buffer = lock.lock().unwrap();
                while buffer.len() == buffer.capacity() {
                    buffer = cvar.wait(buffer).unwrap();
                }
                buffer.push(item);
                cvar.notify_one();
            }
        })
    }).collect();

    let consumers: Vec<_> = (0..num_consumers).map(|i| {
        let buffer = Arc::clone(&buffer);
        thread::spawn(move || {
            loop {
                let (lock, cvar) = &*buffer;
                let mut buffer = lock.lock().unwrap();
                while buffer.is_empty() {
                    buffer = cvar.wait(buffer).unwrap();
                }
                let item = buffer.remove(0);
                cvar.notify_one();
                println!("Consumer {}: Consumed item - {}", i, item);
            }
        })
    }).collect();

    for producer in producers {
        producer.join().unwrap();
    }
    for consumer in consumers {
        consumer.join().unwrap();
    }
}
