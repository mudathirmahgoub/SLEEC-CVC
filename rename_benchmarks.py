import os
path = "test_files_quantifiers"
files = [
    os.path.join(dp, f)
    for dp, _, filenames in os.walk(path)
    for f in filenames
    if os.path.splitext(f)[1] == ".smt2"
]

import os
for file in files:
  name = file.replace("test_files_quantifiers","")
  name = name.replace("/", "_")  
  name = name.replace("test_files_","")  
  print (name)
  os.rename(file, "smtlib_quantifiers/{}".format(name))