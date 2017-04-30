""" solver.py is the interface of Cosette.
    solve takes Cosette source code and returns a json object containing the
    result computed from the Cosette solver.
"""
from subprocess import Popen, PIPE, STDOUT
import tempfile
import time
import json

def solve(cos_source):
    """ return the result of runing a cosette query
    """
    coq_parse, coq_out = gen_coq(cos_source)
    ros_parse, ros_out = gen_rosette(cos_source)

    ret = {
        'coq_html': "",
        'rosette': {
            'html': "",
            'json': {}
        }
    }

    if coq_parse and ros_parse:
        # write coq and rosette code to temp files
        coq_file = tempfile.NamedTemporaryFile()
        coq_file.write(coq_out)
        coq_file.seek(0)
        ros_file = tempfile.NamedTemporaryFile()
        ros_file.write(ros_out)
        ros_file.seek(0)

        cmd_coq = './coq_solve.sh ' + coq_file.name
        cmd_ros = './rosette_solve.sh ' + ros_file.name
        running_procs = [(Popen(cmd_coq, shell=True, stdout=PIPE, stderr=PIPE), 0),
                         (Popen(cmd_ros, shell=True, stdout=PIPE, stderr=PIPE), 1)]
        results = ["", ""]
        while running_procs:
            for proc in running_procs:
                retcode = proc[0].poll()
                if retcode is not None:
                    running_procs.remove(proc)
                    results[proc[1]] = proc[0].stdout.read() + proc[0].stderr.read()
                else:
                    time.sleep(.1)
                    continue
        return parse_results(results)
    else: # either coq_parse or ros_parse is False
        if coq_parse:
            ret["coq_html"] = "Coq code generation succeed."
        else:
            ret["coq_html"] = coq_out
        if ros_parse:
            ret["rosette"]["html"] = "Rosette code generation succeed."
        else:
            ret["rosette"]["html"] = ros_out
        return json.dumps(ret)


def gen_rosette(cos_source):
    """ generate rosette code given a cosette program and filename.
        return (True, <rosette code>) or (False, <error message>).
    """
    prog = "dsl/dist/build/RosetteCodeGen/RosetteCodeGen"
    proc = Popen(prog, shell=True, stdin=PIPE, stdout=PIPE, stderr=STDOUT)
    output = proc.communicate(input=cos_source.encode())[0]
    if proc.returncode != 0:
        return (False, "Internal Error (to rosette). \n {}".format(output))
    elif "error" in output.lower():
        return (False, "Syntax Error. \n {}".format(output))
    return (True, output)

def gen_coq(cos_source):
    """ generate coq cod given cosette program and filename.
        return (True, <coq code>) or (False, <error message>)
    """
    prog = "dsl/dist/build/CoqCodeGen/CoqCodeGen"
    proc = Popen(prog, shell=True, stdin=PIPE, stdout=PIPE, stderr=STDOUT)
    output = proc.communicate(input=cos_source.encode())[0]
    if proc.returncode != 0:
        return (False, "Internal Error (to rosette). \n {}".format(output))
    elif "error" in output.lower():
        return (False, "Syntax Error. \n {}".format(output))
    return (True, output)


def parse_results(results):
    """ Parse the results of Coq and Rosette execution.
    """
    coq_result, ros_result = results
    if "error" in coq_result:
        if "attempt to save an incomplete proof" in coq_result:
            coq_ret = "Query equivalence unknown."
        elif "syntax error" in coq_result:
            coq_ret = "Invalid Coq Code."
    else:
        coq_ret = "Success. Queries are equivalent."
    json_dict = {
        'coq_html': coq_ret,
        'rosette': {
            'html': "",
            'json': json.loads(ros_result)
        }
    }

    return json.dumps(json_dict)
