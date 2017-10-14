"""
run calcite examples in batch
"""
import solver
import os.path
import json
import gen_cos_files

def run_calcite_examples(write=False):
    """ run calcite examples """
    calcite_path = "./examples/calcite/"

    # get already generated rules, since some of them may be edited
    generated_rules = {}
    for filename in os.listdir(calcite_path):
        if filename.endswith(".cos"):
            case_name = filename[:-4]
            with open(calcite_path+filename, 'r') as source_file:
                cos = source_file.read()
                generated_rules[case_name] = cos

    # run all the rule from the json file
    with open(calcite_path+'calcite_tests.json') as input_file:
        calcite_rules = json.load(input_file)

    for rule in calcite_rules:
        rname = rule["name"]
        if rname in generated_rules:
            cos = generated_rules[rname]
        else:
            cos = gen_cos_files.gen_cos_source(rule["q1"], rule["q2"])

        result = json.loads(solver.solve(cos))
        print "{},{}".format(rname, result["result"])


if __name__ == '__main__':
    run_calcite_examples()
