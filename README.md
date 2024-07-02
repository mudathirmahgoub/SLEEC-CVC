# This is a experimental repo of SLEEC analyzer using CVC5 as the backend solver.

## Installation:
1. Install Python3 (3.5 -3.11) 
2. Follow instructions in https://github.com/cvc5/cvc5/blob/main/INSTALL.rst to install CVC5 with python binding
3. `pip3 install textx`
4. `pip3 install argparse`
5. run `python3 sleec_cvc5.py test_files/test.sleec redundancy` to observe result


## structure
1. sleec_cvc5.py is the top level script to be called for Sleec analysis
2. sleecParse_cvc.py parses input sleec content and generate SLEEC AST 
3. CVC5_wrapper contains scripts to convert SLEEC ASTs into CVC5 constraints
   4. cvc_wrapper.py is my own constraint generation interface that wraps around CVC5 python API to communicate with CVC5
   5. sleec_to_cvc5.py translates SLEEC ASTs into CVC5 constraints through cvc_wrapper.py
6. test_files contains sleec test files