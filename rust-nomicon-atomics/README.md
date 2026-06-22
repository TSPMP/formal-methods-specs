# Rust Nomicon Atomics Specifications

The specifications in that directory are supposed to model the minimal
[example](https://doc.rust-lang.org/nomicon/atomics.html#hardware-reordering)
about hardware reordering in the Rust nomicon's atomics chapter.

For ease of reference, here is the code that we assume a compiler outputs with
no reorderings from the compiler
```
initial state: x = 0, y = 1

THREAD 1        THREAD 2
y = 3;          if x == 1 {
x = 1;              y *= 2;
                }
```

The models are

- `NoHwReorderNoMemHier.tla`: This models the execution without hardware
  reordering and without memory hierarchies. This shows that y can end in the
  states y=3 or y=6.
- `HwReorderNoMemHier.tla`: This modeled hardware reordering but without memory
  hierarchies and it showed that this is not enough to get the end state y=2.
- `HwReorderMemHier.tla`: Modeling both hardware reordering and a memory
  hierarchy shows that the not obvious y=2 end state can be reached. The model
  checker gives a nice trace when this happens if you check the `Correctness`
  condition without y=2 as part of it.

To verify the `Correctness` property of the models, you will need the
tla2tools.jar from the TLA+ tools
[releases](https://github.com/tlaplus/tlaplus/releases) and run, e.g.
```
$ java -cp tla2tools.jar tlc2.TLC -config HwReorderMemHier.cfg HwReorderMemHier.tla
```
