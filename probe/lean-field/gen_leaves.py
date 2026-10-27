"""Write a chain checker input at a shape: 2^r pseudo-random 32-byte starts, chain length n.
The root is not computed: chaincheck then prints `mismatch NS`, and NS (the time of the full
recomputation, chains, leaf statements and tree root) is what is measured."""
import hashlib, json, sys
r, n, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
starts = [hashlib.blake2s(b"probe-start-%d" % i).hexdigest() for i in range(1 << r)]
json.dump({"n": n, "starts": starts}, open(out, "w"))
