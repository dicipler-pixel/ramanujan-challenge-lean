# SCRIPT: RAM-FACES-BUILD-HTML
import markdown, base64, re, sys
src = sys.argv[1]; out = sys.argv[2]
md = open(src, encoding='utf-8').read()
body = markdown.markdown(md, extensions=['tables'])
png = base64.b64encode(open('pkg/fig_faces.png','rb').read()).decode()
body = body.replace('src="fig_faces.png"', 'src="data:image/png;base64,%s"' % png)
body = re.sub(r'<a href="(http[^"]+)"', r'<a href="\1" rel="noopener"', body)
css = '''
:root{--bg:#fbfaf7;--fg:#1c1b19;--mut:#5f5b53;--line:#d9d5cb;--acc:#8a5a00;--card:#f3f0e8}
@media (prefers-color-scheme:dark){:root{--bg:#0f1014;--fg:#e9e6de;--mut:#a39f95;--line:#2b2d36;--acc:#f2b84b;--card:#171922}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);font:17px/1.6 Georgia,'Iowan Old Style','Times New Roman',serif}
main{max-width:860px;margin:0 auto;padding:40px 22px 80px}
h1{font-size:2.05rem;line-height:1.2;margin:0 0 .4em}
h2{font-size:1.4rem;margin:2.2em 0 .5em;padding-top:.6em;border-top:1px solid var(--line)}
h3{font-size:1.12rem;margin:1.6em 0 .4em;color:var(--acc)}
p,li{max-width:74ch}
table{border-collapse:collapse;width:100%;margin:1em 0;font-size:.93rem;font-family:system-ui,-apple-system,'Segoe UI',sans-serif}
th,td{border-bottom:1px solid var(--line);padding:7px 9px;text-align:left;vertical-align:top}
th{color:var(--mut);font-weight:600}
code{font:0.88em ui-monospace,Menlo,Consolas,monospace;background:var(--card);padding:1px 5px;border-radius:4px}
img{width:100%;height:auto;border-radius:8px;margin:1em 0}
hr{border:0;border-top:1px solid var(--line);margin:1.6em 0}
a{color:var(--acc)}
em{color:var(--mut)}
'''
html = '<!DOCTYPE html>\n<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><title>Ramanujan\'s Gamma Fractions Read as Stacks of Faces</title><style>%s</style></head><body><main>%s</main></body></html>' % (css, body)
open(out,'w',encoding='utf-8').write(html); print(len(html))
