""" solver.py is the interface of Cosette.
    solve takes Cosette source code and returns a json object containing the
    result computed from the Cosette solver.
"""
from subprocess import Popen, PIPE, STDOUT
import tempfile
import time
import json

def solve(cos_source, cos_folder=".", show_compiled=False):
    """ cos_source: Cosette source code, in string
        cos_folder: path of cosette folder, default is current "."
        return the result of runing a cosette query
    """
    coq_parse, coq_out = gen_coq(cos_source, cos_folder)
    ros_parse, ros_out = gen_rosette(cos_source, cos_folder)

    ret = {
        "result": "",           # can be EQ, NEQ, UNKNOWN, ERROR
        "coq_result": "",       # can be EQ, UNKNOWN, ERROR, STOPED
        "coq_log": "",          # log of the Coq execution
        "rosette_log": "",      # log of the Rosette execution
        "rosette_result": "",   # can be NEQ, UNSAT, STOPED
        "counterexamples": [],  # counterexamples
        "error_msg": "",        # error message
    }

    if coq_parse and ros_parse:
        # write coq and rosette code to temp files
        coq_file = tempfile.NamedTemporaryFile()
        coq_file.write(coq_out)
        coq_file.seek(0)
        ros_file = tempfile.NamedTemporaryFile()
        ros_file.write(ros_out)
        ros_file.seek(0)

        cmd_coq = 'cd {}; ./coq_solve.sh '.format(cos_folder) + coq_file.name
        cmd_ros = 'cd {}; ./rosette_solve.sh '.format(cos_folder) + ros_file.name
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
        ret = parse_results(results)
    else: # either coq_parse or ros_parse is False
        if coq_parse: # then rosette must not parse
            ret["coq_log"] = "Coq code generation succeed."
            ret["coq_result"] = "STOPED"
        else:
            ret["coq_log"] = coq_out
            ret["coq_result"] = "ERROR"
        if ros_parse: # then Coq must not parse
            ret["rosette_log"] = "Rosette code generation succeed."
            ret["rosette_result"] = "STOPED"
        else:
            ret["rosette_log"] = ros_out
            ret["rosette_result"] = "ERROR"

        # put overall error message
        if (not coq_parse) and (not ros_parse):
            # probably an error on parsing Cosette AST
            # only show one error here
            ret["error_msg"] = "Syntax Error. \n {}".format(coq_out)
        elif coq_parse: # only coq_parse is true
            ret["error_msg"] = "Rosette Error. \n {}".format(ros_out)
        else: # only ros_parse is true
            ret["error_msg"] = "Coq Error \n {}".format(coq_out)

    # add coq and rosette source code if required
    if show_compiled:
        if coq_parse:
            ret["coq_source"] = coq_out
        if ros_parse:
            ret["rosette_source"] = ros_out

    return json.dumps(ret)


def gen_rosette(cos_source, cos_folder):
    """ generate rosette code given a cosette program and filename.
        return (True, <rosette code>) or (False, <error message>).
    """
    prog = "{}/dsl/dist/build/RosetteCodeGen/RosetteCodeGen".format(cos_folder)
    proc = Popen(prog, shell=True, stdin=PIPE, stdout=PIPE, stderr=STDOUT)
    output = proc.communicate(input=cos_source.encode())[0]
    if proc.returncode != 0:
        return (False, "Internal Error (to rosette). \n {}".format(output))
    elif "error" in output.lower():
        return (False, "Syntax Error. \n {}".format(output))
    return (True, output)

def gen_coq(cos_source, cos_folder):
    """ generate coq cod given cosette program and filename.
        return (True, <coq code>) or (False, <error message>)
    """
    prog = "{}/dsl/dist/build/CoqCodeGen/CoqCodeGen".format(cos_folder)
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
    coq_result = coq_result.lower()
    ret = {}
    # put Coq result
    if "error" in coq_result:
        if "attempt to save an incomplete proof" in coq_result:
            ret["coq_result"] = "UNKNOWN"
            ret["coq_log"] = ""
        elif "syntax error" in coq_result:
            ret["coq_result"] = "ERROR"
            ret["coq_log"] = "Invalid generated Coq code. Please file an issue."
    else:
        ret["coq_result"] = "EQ"
        ret["coq_log"] = ""     # nothing

    # put rosette result
    try:
        ros_json = json.loads(ros_result)
        ret["rosette_result"] = ros_json["status"]
        if ros_json["status"] == "NEQ":
            ret["counterexamples"] = ros_json["counter-example"]
        else:
            ret["rosette_log"] = ""
    except ValueError:
        ret["rosette_result"] = "ERROR"
        ret["rosette_log"] = ros_result # just dump the raw error message here

    # combine Coq and rosette results
    if ret["coq_result"] == "UNKNOWN" and ret["rosette_result"] == "NEQ":
        ret["result"] = "NEQ"
    elif ret["coq_result"] == "EQ" and ret["rosette_result"] == "UNSAT":
        ret["result"] = "EQ"
    elif ret["coq_result"] == "EQ" and ret["rosette_result"] == "NEQ":
        ret["result"] = "ERROR"
        ret["error_msg"] = "Coq and Rosette executions doesn't agree. File an issue!"
    else:
        ret["result"] = "ERROR"
        ret["error_msg"] = "{} \n \n {}".format(ret["coq_log"], ret["rosette_log"])

    return ret
