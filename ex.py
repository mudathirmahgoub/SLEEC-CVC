import subprocess
import os

for i in range(1,100):
  command = 'find ./ -name "{:03}.smt2" | xargs rm -r'.format(i)
  print (command)
  os.system(command)    