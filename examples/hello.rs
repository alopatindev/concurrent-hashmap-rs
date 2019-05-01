use concurrent_hashmap::hashmap::HashMap;
use std::sync::Arc;
use std::thread;

fn main() {
    let map: HashMap<i32, String> = HashMap::new();
    let map = Arc::new(map);

    let mut threads = vec![];
    let threads_num = 8;

    for key in 0..threads_num {
        let map = map.clone();
        threads.push(thread::spawn(move || {
            let value = format!("value of {}", key);
            map.insert(key, value);
        }));
    }

    for key in (0..threads_num).filter(|k| k % 2 == 0) {
        let map = map.clone();
        threads.push(thread::spawn(move || match map.remove(&key) {
            Some(value) => println!("removed {}", value),
            None => (),
        }));
    }

    for key in 0..threads_num {
        let map = map.clone();
        threads.push(thread::spawn(move || match map.get(&key) {
            Some(value) => println!("{} -> {}", key, value),
            None => (),
        }));
    }

    for thread in threads {
        thread.join().unwrap();
    }
}
