# Dur

***DUR (Default UArc Runner)**, an interpreter and linker implementing the UArc specification.*

It aims to:
* Be well-rounded and suitable for standard usage.
* Be no-libstd and dependency-free.
* Leverage as less libcore internals (implementation details) as possible.
* Be portable; being able to be run on popular Unix-like OSes.
* Be as fast as possible without generating machine code,
  meaning that it won't abstract upon memory, syscalls, etc.

## How to Build

**NOTE:** Dur is still under development and will building it with these instructions will thus output a debug executable by default.

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

## License

Dur is licensed under an Apache-2.0 license.
See it [here](LICENSE).
