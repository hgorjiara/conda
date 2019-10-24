import os
import sys
import random
import re

import os

path = './'
def getFilesList():
	files = []
	for r, d, f in os.walk(path):
		for file in f:
			if '.log' in file:
				files.append(os.path.join(r, file))
	return files

def analyzeExecution():
	for myfile in getFilesList():
		print(myfile)
		with open(myfile, "r") as f:
			line = f.readline()
			while line:
				if 'PycoSAT SOLVING TIME' in line:
					line = f.readline()
					time =re.findall("\d+\.\d+", line)
					if float(time[0]) > 1:
						print (line)
				line = f.readline()
		

def main():
	analyzeExecution()

if __name__ == "__main__":
    main()
			    
