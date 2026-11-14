from pathlib import Path
import cairosvg
OUT=Path(__file__).resolve().parent.parent/'figs'; OUT.mkdir(exist_ok=True)
W=519; H=260
ink='#203244'; blue='#315F85'; teal='#25828A'; red='#B6534B'; muted='#607386'; line='#B8C5CE'; pale='#EEF3F7'; paleg='#EAF4F3'; paler='#F8EEEC'; white='#FFFFFF'; gold='#B77D28'

def esc(s): return s.replace('&','&amp;').replace('<','&lt;').replace('>','&gt;')
def start(): return [f'<svg xmlns="http://www.w3.org/2000/svg" width="183mm" height="91.7mm" viewBox="0 0 {W} {H}"><defs><marker id="arr" markerWidth="7" markerHeight="7" refX="6" refY="3.5" orient="auto"><path d="M0,0 L7,3.5 L0,7 Z" fill="{blue}"/></marker><marker id="arrT" markerWidth="7" markerHeight="7" refX="6" refY="3.5" orient="auto"><path d="M0,0 L7,3.5 L0,7 Z" fill="{teal}"/></marker><marker id="arrR" markerWidth="7" markerHeight="7" refX="6" refY="3.5" orient="auto"><path d="M0,0 L7,3.5 L0,7 Z" fill="{red}"/></marker></defs><rect width="519" height="260" fill="white"/>']
def text(x,y,s,size=6,color=ink,weight='400',anchor='middle', extra=''):
    return f'<text x="{x}" y="{y}" text-anchor="{anchor}" font-family="Arial, Helvetica, sans-serif" font-size="{size}" font-weight="{weight}" fill="{color}" {extra}>{esc(s)}</text>'
def box(x,y,w,h,title,sub='',fill=pale,stroke=blue,sz=6):
    a=[f'<g id="{title.lower().replace(" ","-")}"><rect x="{x}" y="{y}" width="{w}" height="{h}" rx="7" fill="{fill}" stroke="{stroke}" stroke-width="1.2"/>']
    if sub:
        parts=sub.split('|')
        a += [text(x+w/2,y+h/2-3,title,sz,ink,'700')]
        if len(parts)==1: a += [text(x+w/2,y+h/2+8,parts[0],5.5,ink)]
        else: a += [text(x+w/2,y+h/2+5,parts[0],5.1,ink),text(x+w/2,y+h/2+13,parts[1],5.1,ink)]
    else:a += [text(x+w/2,y+h/2+2,title,sz,ink,'700')]
    a+=['</g>']; return ''.join(a)
def arrow(x1,y1,x2,y2,color=blue,marker='arr',width=1.7,dash=''):
    ds=f' stroke-dasharray="{dash}"' if dash else ''
    return f'<path d="M{x1},{y1} L{x2},{y2}" fill="none" stroke="{color}" stroke-width="{width}" marker-end="url(#{marker})"{ds}/>'
def save(name,s):
    s+='</svg>'; p=OUT/f'{name}.svg'; p.write_text(s,encoding='utf8'); cairosvg.svg2png(bytestring=s.encode(),write_to=str(OUT/f'{name}.png'),output_width=2595)

# Figure 1: protocol path and distinct threat entry points
s=start(); s += [text(18,20,'REPORT',6,muted,'700','start'),box(30,54,115,66,'Smart meters','(CT_i, sigma_i) · signed reports',pale,blue,7),box(200,54,112,66,'AG','aggregate CT, sigma; publish t_n',pale,blue,7),box(367,54,120,66,'CC','verify · decrypt · peel',paleg,teal,7),box(370,160,114,48,'Statistics','Mhat_j, Qhat_j',white,line,6)]
s += [arrow(145,87,198,87),arrow(312,87,365,87),arrow(427,120,427,158,teal,'arrT')]
s += [text(171,76,'1',6,blue,'700'),text(338,76,'2',6,blue,'700'),text(437,143,'3',6,teal,'700')]
# Attack A injects at AG aggregate output; B at meter input
s += [f'<circle cx="255" cy="36" r="10" fill="{paler}" stroke="{red}" stroke-width="1.2"/>',text(255,38,'A',6,red,'700'),arrow(255,46,255,52,red,'arrR',1.4),text(287,39,'known shift Δ at aggregate',5.5,red,'400','start')]
s += [f'<circle cx="30" cy="143" r="10" fill="{paler}" stroke="{red}" stroke-width="1.2"/>',text(30,145,'B',6,red,'700'),arrow(40,143,61,121,red,'arrR',1.4),text(52,158,'out-of-capacity report',5.5,red,'400','start')]
s += [text(30,231,'BLS signatures + t_n',5.5,muted,'400','start'),text(487,231,'τ check after mask removal',5.5,teal,'700','end')]
save('fig1_system', ''.join(s))

# Figure 2: blinded ciphertext check vs plaintext check
s=start(); s += [text(16,20,'A',7,blue,'700','start'),text(34,20,'Existing mask check',7,ink,'700','start'),text(16,138,'B',7,teal,'700','start'),text(34,138,'Plaintext check digit',7,ink,'700','start')]
# top path
s += [box(24,40,128,55,'Modified ciphertext','CT′ = CT*(1+N)^Delta',pale,blue,6),box(197,40,130,55,'Exponentiate by N','(CT′)^N = CT^N',white,line,6),box(370,40,125,55,'t_n accepts','message shift vanishes',paleg,teal,6),arrow(152,68,195,68),arrow(327,68,368,68,teal,'arrT')]
s += [text(259,111,'(1+N)^(NΔ) ≡ 1  (mod N^2)',6,muted)]
# bottom path
s += [box(24,160,128,55,'Decrypt and peel','Mhat, Qhat, tauhat',pale,blue,6),box(197,160,130,55,'Recompute check','tauhat ?= sum(c*Mhat + cprime*Qhat)|mod P',white,line,5.5),box(370,160,125,55,'Fixed nonzero Δ','reject with ≥ 1−1/P',paler,red,5.8),arrow(152,188,195,188),arrow(327,188,368,188,red,'arrR')]
s += [text(259,238,'Requires A3–A4: coefficients hidden until the deviation is fixed; in-range slots; no target-domain leakage.',5.4,muted)]
save('fig2_paths',''.join(s))

# Figure 3: independent domains and out-of-band seed provisioning
s=start(); s += [text(18,20,'DOMAIN-PARALLEL AGGREGATION',6,muted,'700','start')]
# meters grouped into repeated domains
for x,label in [(25,'Domain 1'),(195,'Domain 2'),(365,'Domain m')]:
    s += [f'<g id="{label.lower().replace(" ","-")}"><rect x="{x}" y="42" width="128" height="112" rx="8" fill="white" stroke="{line}" stroke-width="1.1"/>',text(x+64,57,label,6.2,ink,'700')]
    for i in range(3):
        xx=x+20+i*36
        s += [f'<rect x="{xx}" y="69" width="28" height="22" rx="4" fill="{pale}" stroke="{blue}" stroke-width=".8"/>',text(xx+14,83,'SM',5.2,blue,'700')]
    s += [text(x+64,103,'... x b meters ...',5.3,muted),text(x+64,119,'capacities: b*h_j, b*h_j^2',5.5,ink),text(x+64,135,'independent mask + tau',5.2,teal,'700'),'</g>']
s += [text(169,99,'...',5.5,muted),text(339,99,'...',5.5,muted)]
# arrows to per-domain ciphertext outputs
for x in (89,259,429):
    s += [arrow(x,154,x,173,blue,'arr',1.2),box(x-39,177,78,30,'1 ciphertext','per domain',pale,blue,5.5)]
s += [text(18,224,'m = ceil(n/b) domains',5.5,ink,'700','start'),text(181,224,'Independent capacities localize rejection to ≤ b meters',5.5,ink,'400','start')]
# seed distribution separate from data path
s += [box(23,232,90,22,'CC: derive seed','domain, epoch',paleg,teal,5.2),box(203,232,108,22,'mTLS 1.3','32-byte τ seed',white,line,5.2),box(404,232,92,22,'Authorized SMs','derive coefficients',pale,blue,5.2),arrow(113,243,201,243,teal,'arrT',1.15),arrow(311,243,402,243,teal,'arrT',1.15)]
save('fig3_chunk',''.join(s))
