from argparse import ArgumentParser

from sleecParser_cvc import parse_sleec, check_red, check_conflict, check_concerns


def parse_and_check_conflict(filename):
    model, rules, concerns, purposes, relations, Action_Mapping, Actions = parse_sleec(filename,
                                                                                       read_file=True)
    res = check_conflict(model, rules, relations, Action_Mapping, Actions, check_proof=False, profiling=False)
    return res


def parse_and_check_red(filename):
    model, rules, concerns, purposes, relations, Action_Mapping, Actions = parse_sleec(filename,
                                                                                       read_file=True)
    res = check_red(model, rules, relations, Action_Mapping, Actions, check_proof=False,profiling=False)
    return res


def parse_and_check_concern(filename):
    model, rules, concerns, purposes, relations, Action_Mapping, Actions = parse_sleec(filename,
                                                                                       read_file=True)
    res = check_concerns(model, rules, concerns, relations, Action_Mapping, Actions)
    return res


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument('--filename', help="SLEEC file to analyze", type=str)
    parser.add_argument('--analysis', help='What the analysis to run: redundancy/conflict/concern', type=str)
    args = parser.parse_args()
    supported_mode = {"redundancy": parse_and_check_red, "conflict": parse_and_check_conflict,
                      "concern": parse_and_check_concern}
    analysis = args.analysis
    if analysis not in supported_mode:
        print("unsupported analysis mode, please choice one of the analysis mode redundancy/conflict/concern")
        print("running redundancy for default")
    analysis_func = supported_mode.get(analysis, parse_and_check_red)
    analysis_func(args.filename)
