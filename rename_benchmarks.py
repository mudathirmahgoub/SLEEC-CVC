import os
path = "test_files_filters"
files = [
    os.path.join(dp, f)
    for dp, _, filenames in os.walk(path)
    for f in filenames
    if os.path.splitext(f)[1] == ".smt2"
]

import os
for file in files:
  name = file.replace("/home/mudathir/Desktop/SLEEC-CVC/test_files_filters","")
  name = name.replace("/", "_")  
  name = name.replace("test_files_","")  
  print (name)
  os.rename(file, "smtlib_filters/{}".format(name))