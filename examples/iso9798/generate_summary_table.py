#!/usr/bin/env python

def get_files():
    import os

    flo = []
    fl = os.listdir(".")
    for fn in fl:
        if fn.endswith(".spthy"):
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
        return latex + " (UDK)"
    args = ",".join(dt[2:])
    if args in ["1","2"]:
        args = "Option %s" % (args)
    return "%s (%s)" % (latex, args)

def latex_claim(txt,r2,args):

    largs = []
    for it in args:
        if len(it) <= 1:
            largs.append(it)
        else:
            largs.append("\\mathit{%s}" % (it.strip()))
    ltargs = "$%s$" % (", ".join(largs))

    if txt == "iagree":
        return "Injective agreement with $%s$ on %s" % (r2,ltargs)
    elif txt == "niagree":
        return "Non-injective agreement with $%s$ on %s" % (r2,ltargs)
    else:
        return "%s $%s$ (%s)" % (txt,r2,ltargs)

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

            table[protname] = {}
            print "Found protocol", protname

        elif l.startswith("niagree") or l.startswith("iagree"):
            # Must be a claim
            if protname == None:
                print "Hmm, no protocol for this claim. Weird."
            else:
                claim = (l.split("(")[0]).strip()
                roles = l.split("_")
                r1 = roles[0][-1]
                r2 = roles[1][-1]
                l1 = l.find("[")
                l2 = l.find("]")
                args = l[l1+1:l2]
                table[protname]["src"] = l
                table[protname]["claim"] = claim
                table[protname]["r1"] = r1
                table[protname]["r2"] = r2
                table[protname]["args"] = args.split(",")

    fp.close()
    return table

def latex_table(table):
    """
    Turn the previous table into latex
    """
    k = sorted(table.keys())
    res = "\\begin{tabular}{lll}\n"
    res += "Protocol & Role & Property \\\\ \n"
    res += "\\hline \n"
    for pn in k:
        res += "%s & " % (latex_name(pn))
        dt = table[pn]
        res += "$%s$ & " % (dt["r1"])
        res += latex_claim(dt["claim"], dt["r2"], dt["args"])
        res += " \\\\ \n"

    res += "\\hline \n"
    res += "\\end{tabular}\n"
    return res


def main():
    import sys

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
