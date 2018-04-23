# Origin

_(We have obtained these benchmarks from https://github.rcac.purdue.edu/cap/DryadSynth/tree/master/benchmarks/INV2)_

There benchmarks are adapted from [FiB](https://github.com/spencerxiao/ase2017-results-and-tools/tree/master/FiB_Tool/benchmarks) 

However, all benchmarks with modular assertions in program body is not included.

# Duplicate

These benchmarks are marked as a similar duplicate to a already included one,
thus not included again

- `32_x.impp`

# Over-Complex

These benchmarks are marked over-complex to convert to SyGuS format. Conversion 
is possible, but as indicated, too complex.

- `12n_x.impp`

# Failure of validation

These benchmarks did not pass the SyGuS-INV benchmark validation. However they're
recognizable to our parser and our solver could handle them properly. This could
be due to the bugs in the SyGuS-INV benchmark validator. We may wait for these to
be fixed or tweak our benchmarks to work around these.

- `fib_04.sl`
- `fib_07.sl`
- `fib_08.sl`
- `fib_09s.sl`
- `fib_10.sl`
- `fib_20.sl`