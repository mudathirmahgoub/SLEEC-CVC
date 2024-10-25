import common
import subprocess
import os
import ntpath

last_file = None
if common.RESUME:
    csv_file = open(common.CSV_FILE, "r")
    lines = csv_file.readlines()
    last_file = lines[-1].split(",")[0]
    csv_file.close()

else:
    csv_file = open(common.CSV_FILE, "w")
    csv_file.write("file,mode,rule,result,duration\n")
    csv_file.close()


modes = ["redundancy", "conflict", "concern"]
path = common.PATH
files = [
    os.path.join(dp, f)
    for dp, _, filenames in os.walk(path)
    for f in filenames
    if os.path.splitext(f)[1] == ".sleec"
]

if common.RESUME:
    files = files[files.index(last_file) +1 :]

for file in files:
    for mode in modes:
        dir, name = ntpath.split((file))
        name = name.replace(".sleec", "")
        path = "{}/{}/{}".format(os.getcwd(), dir, name)
        output_file = "{}/output_{}.txt".format(path, mode)
        command = "python3 sleec_cvc5.py --filename {} --analysis {}".format(file, mode)
        print(command)
        p = subprocess.run(
            ["python3", "sleec_cvc5.py", "--filename", file, "--analysis", mode],
            capture_output=True,
            text=True,
        )
        out = open(output_file, "w")
        out.write(p.stdout)
        out.close()
