#!/usr/bin/env python
"""
Generate a summary latex table with all the authentication claims in the .spthy
theory files in this directory.

WARNING: There are no checks that the claims are *correct*, and the user of the
resulting table is responsible for checking that all these claims actually are
successfully proven by scyther-proof.

Author: Cas Cremers
Date:   June 2012
"""

def get_files(filt=None):
    import os

    flo = []
    fl = os.listdir(".")
    for fn in fl:
        if fn.endswith(".spthy"):
            if filt == None:
                flo.append(fn)
            else:
                if filt in fn:
                    flo.append(fn)
    return flo

def latex_name(pn):
    """
    Return a clean latex version of a protocol name or None if we need to skip it
    """
    dt = pn.split("_")
    part = dt[0]
    mech = dt[1]
    latex = "9798-%s-%s" % (part,mech)
    if len(dt) == 2:
        return latex
    if dt[2] == "bdkey":
        return latex
    if dt[2] == "udkey":
        return latex + " (\\UnidirectionalKeys)"

    args = ",".join(dt[2:])

    if "special" in args:
        return "%s (\\DisjointRoles)" % (latex)
    if args in ["1","2"]:
        args = "Opt. %s" % (args)
    
    return "%s (%s)" % (latex, args)


def latex_arg(x):
    """
    Clean up an argument for use in math mode.
    """
    arg = x.strip()
    sub = ""
    if not arg.startswith("Text"):
        arg = arg.upper()

    # Special case
    if arg == "RPA":
        return "R'_A"

    # Determine subscript
    cnt = 0
    for i in range(1,len(arg)):
        if arg[len(arg)-i] in ["A","B","P"]:
            cnt += 1
        else:
            break
    if cnt > 0:
        sub = arg[-cnt:]
        arg = arg[:-cnt]
    
    # Finally, mathit if needed
    if len(arg) > 2:
        arg = "\\mathit{%s}" % (arg)
    if len(sub) > 2:
        sub = "\\mathit{%s}" % (sub)

    if len(sub) == 0:
        return arg
    else:
        return "%s_{%s}" % (arg,sub)


def latex_args(args):
    """
    Clean up a list of arguments for use in math mode.
    """
    largs = []
    for x in args:
        largs.append(latex_arg(x))
    ltargs = "$%s$" % (", ".join(largs))
    return ltargs


def latex_claim(txt,r2,args):
    """
    Return a three-column version (property, with, data) for a latex table
    """

    ltargs = latex_args(args)

    if txt == "iagree":
        return "Injective agreement & $%s$ & %s" % (r2,ltargs)
    elif txt == "niagree":
        return "Non-injective agreement & $%s$ & %s" % (r2,ltargs)
    else:
        return "%s & $%s$ & %s" % (txt,r2,ltargs)

def parse_file(table,fn):
    """
    Parse a file and add the data to the table.

    Table is a dict from protocol name to a dict.
    The dict then has the following fields:
    - 
    """
    boring = "isoiec_9798_"
    protname = None
    fp = open(fn,'r')
    buf = ""
    for rawl in fp.xreadlines():
        l = buf + rawl.strip()
        if l.endswith("->"):
            buf = l + " "
            continue

        if buf != "":
            print "Joined up lines to form:"
            print l
        buf = ""

        if l.startswith("property") or l.startswith("properties"):
            # Property of ... protocol name
            protname = l.split()[-1]
            if protname[-1] == ")":
                protname = protname[:-1]

            if protname.startswith(boring):
                protname = protname[len(boring):]

            table[protname] = []
            print "Found protocol", protname

        elif l.startswith("niagree") or l.startswith("iagree"):
            # Must be a claim
            if protname == None:
                print "Hmm, no protocol for this claim. Weird."
            else:
                claimname = (l.split("(")[0]).strip()
                roles = l.split("_")
                r1 = roles[0][-1]
                r2 = roles[1][-1]
                l1 = l.find("[")
                l2 = l.find("]")
                args = l[l1+1:l2]
                claim = {}
                claim["src"] = l
                claim["claim"] = claimname
                claim["r1"] = r1
                claim["r2"] = r2
                claim["args"] = args.split(",")
                table[protname].append(claim)

    fp.close()
    return table

def latex_table(table):
    """
    Turn the previous table into latex
    """
    k = sorted(table.keys())
    res = "\\begin{tabular}{@{}lclcl@{}}\n"
    res += "\\toprule \n"
    res += "Repaired protocol & Role & Property & With & Data \\\\ \n"
    res += "\\midrule \n"
    for pn in k:
        name = latex_name(pn)
        for claim in table[pn]:
            res += "%s & " % (name)
            name = ""       # Makes for a cleaner table by removing duplicates
            res += "$%s$ & " % (claim["r1"])
            res += latex_claim(claim["claim"], claim["r2"], claim["args"])
            res += " \\\\ \n"

    res += "\\bottomrule \n"
    res += "\\end{tabular}\n"
    return res


def main():
    """
    ./generate_summary_table.py [outputfile] [partfilter]
    """
    import sys

    if len(sys.argv) >= 3:
        fl = get_files(filt=sys.argv[2])
    else:
        fl = get_files()

    table = {}
    for fn in fl:
        print fn
        table = parse_file(table,fn)
    res = latex_table(table)
    print res

    if len(sys.argv) >= 2:
        fn = sys.argv[1]
        fp = open(fn,'w')
        fp.write(res)
        fp.close()
        print "Table written to", fn

if __name__ == '__main__':
    main()
