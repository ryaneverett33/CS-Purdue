#!/usr/bin/env python3

inputs = """qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq
abcd5
aBcDeF
aBcDeFgHiJkLmNoPqRsTuVwXyZaBcDe
aBc9F1
aBcDeFg94JkLmNo8qRsTuVwXyZaBcD2
aBcDeF@
aBcDeF$
AbCdEfGG
aBcDeFgg
aBcDeFgHiJkawfa
abcdefghijkl
AbCdEfGhIjKAWFA
ABCDEFGHIJKL
123456
ab12345f2456gD986f2e35a6f
Exon#Mobi@Le21
123456789abcdef@gDWSS@Aw4
""".split("\n")

outputs = """Error: Password length invalid.
Error: Password length invalid.
11
36
16
41
17
17
3
3
17
14
17
14
8
32
26
21
""".split("\n")

import tempfile
import subprocess

error = False
for i, inp in enumerate(inputs):
    with open("./test-pass", "w") as fp:
        fp.write(inp)
    output = subprocess.Popen(["pwcheck.sh", fp.name],
			      stderr=subprocess.DEVNULL,
			      stdout=subprocess.PIPE).communicate()[0]
    output = output.decode('utf-8')
    if outputs[i] not in output:
        error = True
        print("[!] Invalid output for: " + inp)
        print("Expected: " + outputs[i])
        print("Got:      ", output)

if not error:
    print("All tests passed")
