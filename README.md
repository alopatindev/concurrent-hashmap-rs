# Concurrent HashMap in Rust
[![FOSSA Status](https://app.fossa.io/api/projects/git%2Bgithub.com%2Falopatindev%2Fconcurrent-hashmap-rs.svg?type=shield)](https://app.fossa.io/projects/git%2Bgithub.com%2Falopatindev%2Fconcurrent-hashmap-rs?ref=badge_shield)


```
cargo test
cargo run --example hello
```

## Design Notes
- open addressing
- table resize happens after reaching load factor threshold
    - when new table is being created — all write operations to entries are deferred
        - so new table creation happens without blocking
    - table itself is protected with RwLock
        - as soon as new table is ready — all operations will be blocked just to replace the table and process deferred operations


## License
[![FOSSA Status](https://app.fossa.io/api/projects/git%2Bgithub.com%2Falopatindev%2Fconcurrent-hashmap-rs.svg?type=large)](https://app.fossa.io/projects/git%2Bgithub.com%2Falopatindev%2Fconcurrent-hashmap-rs?ref=badge_large)