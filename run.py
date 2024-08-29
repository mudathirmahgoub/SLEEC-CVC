import subprocess
import os
import ntpath

modes = ["redundancy", "conflict", "concern"]
path = "test_files"
files = [
    os.path.join(dp, f)
    for dp, _, filenames in os.walk(path)
    for f in filenames
    if os.path.splitext(f)[1] == ".sleec"
]
for file in files:
  for mode in modes:
    print(file)
    dir, name = ntpath.split((file))
    name = name.replace(".sleec", "")
    print(dir)
    print(name)

    # subprocess.run(["python3", "sleec_cvc5.py", "--filename", file, "--analysis",  mode]) 