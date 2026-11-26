# Compare each target statement and copied definition, whitespace-normalised, between
# formal-conjectures and this repo. Usage, from a formal-conjectures clone:
#   python3 checks/statements.py FormalConjectures/ErdosProblems/23.lean \
#     FormalConjectures/ErdosProblems/1171.lean \
#     FormalConjecturesForMathlib/SetTheory/Ordinal/PartitionRelation.lean <path to this repo>
import re, sys
up23=open(sys.argv[1]).read(); up1171=open(sys.argv[2]).read(); updef=open(sys.argv[3]).read()
R=sys.argv[4]
n1=open(R+'/ErdosFormalProofs/Erdos23N1.lean').read(); bc=open(R+'/ErdosFormalProofs/Erdos23BlowupC5.lean').read(); mk=open(R+'/ErdosFormalProofs/Erdos1171MonoK.lean').read()
def grab(src, start, end=":= by"):
    i=src.index(start); j=src.index(end, i); return re.sub(r"\s+"," ",src[i+len(start.split()[0]):j]).strip()
def body_after_name(src, name):
    i=src.index(name); j=src.index(":= by", i); return re.sub(r"\s+"," ",src[i+len(name):j]).strip()
pairs=[
 ("erdos_23.variants.n1", body_after_name(up23,"theorem erdos_23.variants.n1"), body_after_name(n1,"theorem erdos_23_n1")),
 ("blowupC5_tight", body_after_name(up23,"theorem blowupC5_tight"), body_after_name(bc,"theorem blowupC5_tight")),
 ("mono_k", body_after_name(up1171,"theorem mono_k "), body_after_name(mk,"theorem mono_k ")),
]
def defn(src,name,stop):
    i=src.index(name); j=src.index(stop,i); return re.sub(r"\s+"," ",src[i:j]).strip()
pairs.append(("def blowupC5", defn(up23,"def blowupC5","\n\n"), defn(bc,"def blowupC5","\n\n")))
pairs.append(("def OrdinalMultiColorRamsey", defn(updef,"def OrdinalMultiColorRamsey","/--"), defn(mk,"def OrdinalMultiColorRamsey","namespace")))
ok=True
for name,a,b in pairs:
    same = a==b; ok&=same
    print(f"{name}: {'identical' if same else 'DIFFERENT'}")
    if not same: print("  upstream:",a,"\n  proofs:  ",b)
print("ALL IDENTICAL" if ok else "DRIFT FOUND")
