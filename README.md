# Concurrent HashMap in Rust

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
