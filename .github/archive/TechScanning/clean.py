from os import path

__cwd__ = path.dirname(__file__)

OPEN = "--*"
CLOSE = "-->"

with open(path.join(__cwd__, "Main.lean"), "r") as f:
    text = f.read().strip()

lines = [x.rstrip() for x in text.splitlines()]

rm: list[int] = []
for i in range(len(lines)):
    if lines[i].strip() == "-->":
        for j in range(i - 1, 0, -1):
            if lines[j] == "":
                rm.append(j)
            else:
                break
        for j in range(i + 1, len(lines)):
            if lines[j] == "":
                rm.append(j)
            else:
                break

keep = (x for x in range(len(lines)) if x not in rm)
lines2 = []
for i in keep:
    line = lines[i]
    if line == CLOSE:
        lines2.extend(("", "", "", CLOSE, ""))
        continue
    lines2.append(line)
print(lines2)


with open(path.join(__cwd__, "Main.lean"), "w") as f:
    f.write("\n".join(lines2))
