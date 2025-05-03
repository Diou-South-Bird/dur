# Dur
## How to Build

Run `make cargo` at this directory to build.
Or run one of the following commands for your OS at this directory to build `dur` from source.

### Linux

```bash
cargo rustc -- -C link-arg=-nostartfiles -C no-redzone=true
```

### Windows

```bash
cargo rustc -- -C link-args="/ENTRY:_start /SUBSYSTEM:console" -C no-redzone=true
```

### macOS

```bash
cargo rustc -- -C link-args="-e __start -static -nostartfiles" -C no-redzone=true
```
