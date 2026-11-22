import math
import ssl, csv, json, os, threading, time, urllib.request, urllib.error, urllib.parse, unicodedata, webbrowser, xml.etree.ElementTree as ET, re
from html.parser import HTMLParser
from html import unescape
from urllib.parse import urljoin, urlparse
from datetime import timedelta, timezone
from http.server import ThreadingHTTPServer, SimpleHTTPRequestHandler
from datetime import datetime
from pathlib import Path

ROOT=Path(__file__).resolve().parent
BASE="https://clima.rs.gov.br/climars/api/v1/ana/cotas/municipio/"
IBGE="https://servicodados.ibge.gov.br/api/v1/localidades/estados/43/municipios"
MUNICIPIOS=["São Borja","Itaqui","Uruguaiana","Manoel Viana","Alegrete","Quaraí","Rosário do Sul","Rio Pardo","Dona Francisca","Estrela","São Sepé","Arroio do Meio","Lajeado","Fontoura Xavier","Pouso Novo","São Gabriel","Cachoeira do Sul","São Jerônimo","Santiago","Bossoroca","Garruchos","Santo Antônio das Missões","São Luiz Gonzaga","São Nicolau","São Francisco de Assis","Candelária","Pantano Grande","Encruzilhada do Sul","Santa Cruz do Sul","General Câmara","Restinga Sêca","Paraíso do Sul","Formigueiro","Vila Nova do Sul","Caçapava do Sul","São Gabriel","Travesseiro","Marques de Souza"]
# Códigos oficiais previamente conhecidos; permitem continuar se o IBGE estiver indisponível.
CODIGOS_FIXOS={"sao borja":"4318002","itaqui":"4310603","uruguaiana":"4322400","alegrete":"4300406","quarai":"4315305","rio pardo":"4315701","estrela":"4307807","lajeado":"4311403","cachoeira do sul":"4303004","rosario do sul":"4316402","sao sepe":"4319604","manoel viana":"4311759","quarai":"4315305","pouso novo":"4315131"}
CACHE={"time":0,"data":None}
LOCK=threading.Lock()
LOCK_SAO_BORJA=threading.Lock()
CACHE_SAO_BORJA={"time":0,"data":None}

def normal(s):
    return "".join(c for c in unicodedata.normalize("NFD",str(s or "").lower()) if unicodedata.category(c)!="Mn").strip()

def getjson(url,timeout=14):
    req=urllib.request.Request(url,headers={"User-Agent":"Mozilla/5.0 Dashboard-Hidrologico-3DE/1.0","Accept":"application/json"})
    with urllib.request.urlopen(req,timeout=timeout) as r:
        return json.loads(r.read().decode("utf-8-sig"))


SACE_URL="https://sace.sgb.gov.br/niveis/estacoes_lista.php?bacia=uruguai"
SACE_BACIA="https://sace.sgb.gov.br/index_bacias_monitoradas.php?getbacia=buruguai"

class SaceTable(HTMLParser):
    def __init__(self):
        super().__init__();self.rows=[];self.row=None;self.cell=None;self.depth=0
    def handle_starttag(self,tag,attrs):
        if tag=='tr':self.row=[]
        elif tag in ('td','th') and self.row is not None:self.cell=[]
        elif tag=='br' and self.cell is not None:self.cell.append(' ')
    def handle_data(self,data):
        if self.cell is not None:self.cell.append(data)
    def handle_endtag(self,tag):
        if tag in ('td','th') and self.cell is not None:
            self.row.append(' '.join(''.join(self.cell).split()));self.cell=None
        elif tag=='tr' and self.row is not None:
            if self.row:self.rows.append(self.row)
            self.row=None

# ID 33 é a estação Passo São Borja no export CSV fornecido pelo usuário.
# A URL de exportação pode mudar no SACE. A descoberta abaixo é conservadora:
# somente aceita um CSV cuja identidade da estação esteja confirmada.
SACE_STATION_ID="33"
SACE_EXPORT_URL="https://sace.sgb.gov.br/niveis/api/dados/uruguai_33_cota.csv"

SACE_PAGES=[
 "https://sace.sgb.gov.br/niveis/estacoes_lista.php?bacia=uruguai",
 "https://sace.sgb.gov.br/index_bacias_monitoradas.php?getbacia=buruguai",
]

def contexto_ssl_sace():
    """TLS validado pelo repositório de certificados do sistema (truststore).
    Nunca desabilita a verificação de certificado ou hostname.
    """
    try:
        import truststore
        return truststore.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    except ImportError:
        pass
    try:
        import certifi
        return ssl.create_default_context(cafile=certifi.where())
    except ImportError:
        return ssl.create_default_context()

def fetch_sace(url, accept='text/html,text/csv,*/*', timeout=12):
    req=urllib.request.Request(url,headers={
      'User-Agent':'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',
      'Accept':accept,'Referer':SACE_BACIA,
      'Cache-Control':'no-cache', 'Accept-Encoding':'identity', 'Connection':'close'})
    with urllib.request.urlopen(req,timeout=timeout,context=contexto_ssl_sace()) as r:
        final=r.geturl()
        if urlparse(final).hostname not in ('sace.sgb.gov.br',):
            raise ValueError('Redirecionamento para domínio não autorizado')
        raw=r.read(3_000_001)
        if len(raw)>3_000_000:raise ValueError('Resposta SACE excede 3 MB')
        return raw,final,r.headers.get('Content-Type','')

def parse_sace_csv(raw):
    for enc in ('utf-8-sig','latin-1'):
        try:conteudo=raw.decode(enc);break
        except UnicodeDecodeError:continue
    if 'data_hora_medicao' not in conteudo[:500].lower() or 'indice' not in conteudo[:500].lower():
        raise ValueError('Resposta não contém cabeçalho CSV esperado')
    linhas=[]
    for row in csv.DictReader(conteudo.splitlines(),delimiter=';'):
        try:
            dt=datetime.strptime(row['data_hora_medicao'].strip(),'%Y-%m-%d %H:%M:%S').replace(tzinfo=timezone(timedelta(hours=-3)))
            cm=float(row['indice'].strip().replace(',','.'))
            if 0<=cm<=3000:linhas.append((dt,cm))
        except (KeyError,ValueError,TypeError):continue
    if not linhas:raise ValueError('CSV sem leituras válidas')
    linhas.sort(key=lambda t:t[0]);return linhas

def montar_estacao_sace(registros,fonte, *, codigo="75780000", nome="Passo São Borja", municipio="São Borja", rio="RIO URUGUAI", inundacao_cm=900, latitude=-28.66, longitude=-56.00):
    instante,cm=registros[-1]
    horas=(datetime.now(timezone(timedelta(hours=-3)))-instante).total_seconds()/3600
    if horas < -1:raise ValueError('Data da medição no futuro')
    antigo=horas>=12
    delta=None;tendencia=None
    anteriores=[(abs((instante-d).total_seconds()-3600),v) for d,v in registros[:-1] if 1800<=(instante-d).total_seconds()<=5400]
    if anteriores:
        _,prev=min(anteriores)
        delta=round(cm-prev,1)
        tendencia=('Subiu ' if delta>0 else 'Desceu ' if delta<0 else 'Estável')+(f'{abs(delta):g} cm na última hora' if delta else ' na última hora')
    else:
        # Quando não há medição de 1 hora atrás, calcula a variação em 24 horas.
        # Prioriza um registro no instante exato; admite aproximação de até 2h,
        # identificando explicitamente que o período é aproximado.
        alvo=instante-timedelta(hours=24)
        candidatos=[(abs((d-alvo).total_seconds()),d,v) for d,v in registros[:-1]
                    if abs((d-alvo).total_seconds())<=7200]
        if candidatos:
            desvio,d_anterior,prev=min(candidatos,key=lambda x:x[0])
            delta=round(cm-prev,1)
            periodo='nas últimas 24 horas' if desvio<=60 else 'em aproximadamente 24 horas'
            if delta>0:
                tendencia=f'Subiu {abs(delta):g} cm {periodo}'.replace('.',',')
            elif delta<0:
                tendencia=f'Desceu {abs(delta):g} cm {periodo}'.replace('.',',')
            else:
                tendencia=f'Estável {periodo}'
    if tendencia is None:
        # Fallback: qualquer par de medições reais recentes da MESMA estação.
        # Não denominar uma diferença de várias horas como variação horária.
        candidatos=[(instante-d,v) for d,v in registros[:-1]
                    if timedelta(minutes=20) <= instante-d <= timedelta(hours=48)]
        if candidatos:
            intervalo,anterior=min(candidatos,key=lambda x:x[0])
            delta=round(cm-anterior,1)
            horas_intervalo=intervalo.total_seconds()/3600
            periodo=(f'em {horas_intervalo:.1f} h' if horas_intervalo < 2
                     else f'em aproximadamente {horas_intervalo:.0f} horas').replace('.',',')
            if delta>0:tendencia=f'Subiu {abs(delta):g} cm {periodo}'
            elif delta<0:tendencia=f'Desceu {abs(delta):g} cm {periodo}'
            else:tendencia=f'Estável {periodo}'
            tendencia=tendencia.replace('.',',')
    return {'codigoEstacao':codigo,'nomeEstacao':nome,'municipio':municipio,
      'rio':rio,'nivelCm':cm,'nivelMetros':cm/100,
      'dataHoraMedicao':instante.strftime('%d/%m/%Y %H:%M:%S'),
      'dataHoraShort':instante.strftime('%d/%m %H:%M'),
      'confiavel':not antigo,'status':'INUNDACAO' if cm>=inundacao_cm else ('DADO_ANTIGO' if antigo else 'NORMAL'),
      'statusLabel':('Inundação (dado antigo)' if antigo else 'Inundação') if cm>=inundacao_cm else ('Dado antigo (SACE)' if antigo else 'Abaixo da inundação'),
      'taxaMudanca':tendencia,'taxaMudancaValor':delta,'fonte':fonte,
      'horasDesdeMedicao':round(horas,1),'dadoAntigo':antigo,
      'latitude':latitude,'longitude':longitude}

def descobrir_csv_sace(html,base):
    """Extrai links explícitos para CSV da estação 33; não adivinha URLs do portal."""
    candidatos=[]
    # Link href e botões que apontem explicitamente ao export CSV da estação 33.
    for m in re.finditer(r'(?:href|data-url)\s*=\s*[\x22\x27]([^\x22\x27<>]+)[\x22\x27]',html,re.I):
        link=unescape(m.group(1)).replace('\\/','/')
        contexto=html[max(0,m.start()-160):m.end()+160].lower()
        if not (('csv' in link.lower() or 'export' in link.lower() or 'download' in link.lower()) and
                (re.search(r'(?<!\d)33(?!\d)',link) or 'passo s' in contexto and 'borja' in contexto)):
            continue
        url=urljoin(base,link)
        if urlparse(url).hostname=='sace.sgb.gov.br' and url not in candidatos:candidatos.append(url)
    return candidatos[:4]

def consultar_sace_sao_borja():
    diag={'fonte':'SACE/SGB','estacao':'Passo São Borja','codigoANA':'75780000',
          'idExportacaoCSV':SACE_STATION_ID,'modo':'consulta HTTP automática a cada 5 minutos','tentativas':[], 'urlConfigurada':SACE_EXPORT_URL}
    urls=[]
    if SACE_EXPORT_URL:
        if urlparse(SACE_EXPORT_URL).scheme=='https' and urlparse(SACE_EXPORT_URL).hostname=='sace.sgb.gov.br':
            urls.append(SACE_EXPORT_URL)
        else:diag['configuracao']='URL configurada inválida (somente HTTPS no SACE)'
    # Endereço confirmado pelo usuário no Firefox (Rede > Cabeçalhos, HTTP 200).
    # A consulta é direta: não depende da descoberta de links em páginas HTML.
    for url in urls[:5]:
        try:
            raw,final,content_type=fetch_sace(url,'text/csv,*/*')
            registros=parse_sace_csv(raw)
            est=montar_estacao_sace(registros,'SACE/SGB (automático)')
            diag.update({'urlCSV':final,'registrosValidos':len(registros),'tipoResposta':content_type,
                'ultimaMedicao':est['dataHoraMedicao'],'nivelCm':est['nivelCm'],
                'horasDesdeMedicao':est['horasDesdeMedicao'],'automatico':True})
            return est,diag
        except Exception as e:diag['tentativas'].append({'csv':url,'erro':str(e)[:200]})
    diag['automatico']=False
    diag['observacao']='Consulta automática ao CSV do SACE falhou. Veja tentativas e erro; CSV local é apenas histórico, não atualização em tempo real.'
    return None,diag


# URL de exportação fornecida pelo usuário a partir do SACE/SGB (Rio Pardo, bacia Guaíba).
RIO_PARDO_SACE_CSV="https://sace.sgb.gov.br/niveis/api/dados/guaiba_55_cota.csv"
def consultar_sace_rio_pardo():
    diag={'fonte':'SACE/SGB','estacao':'Rio Pardo','codigoANA':'85900000',
          'idExportacaoCSV':'guaiba_55','modo':'consulta HTTP automática a cada 5 minutos',
          'urlConfigurada':RIO_PARDO_SACE_CSV,'automatico':False}
    try:
        raw,url,content_type=fetch_sace(RIO_PARDO_SACE_CSV,'text/csv,*/*')
        registros=parse_sace_csv(raw)
        est=montar_estacao_sace(registros,'SACE/SGB (automático)',
             codigo='85900000',nome='Rio Pardo',municipio='Rio Pardo',
             rio='RIO JACUÍ',inundacao_cm=1250,latitude=-29.99,longitude=-52.38)
        diag.update({'automatico':True,'urlCSV':url,'registrosValidos':len(registros),
                     'ultimaMedicao':est['dataHoraMedicao'],'nivelCm':est['nivelCm'],
                     'horasDesdeMedicao':est['horasDesdeMedicao'],
                     'dadoAntigo':est['dadoAntigo']})
        return est,diag
    except Exception as exc:
        diag['erro']=str(exc)[:250]
        diag['observacao']='Não foi possível consultar o SACE; não usar valores inventados ou de outras estações.'
        return None,diag

# Itaqui — estação oficial ANA 75900000, exportação SACE Uruguai (ID 32).
ITAQUI_SACE_CSV="https://sace.sgb.gov.br/niveis/api/dados/uruguai_32_cota.csv"
LOCK_ITAQUI=threading.Lock()
CACHE_ITAQUI={"time":0,"data":None}

def consultar_sace_itaqui():
    diag={'fonte':'SACE/SGB','estacao':'Itaqui','codigoANA':'75900000',
          'idExportacaoCSV':'uruguai_32','urlConfigurada':ITAQUI_SACE_CSV,
          'modo':'consulta automática ao CSV a cada 5 minutos','automatico':False}
    try:
        raw,url,content_type=fetch_sace(ITAQUI_SACE_CSV,'text/csv,*/*')
        registros=parse_sace_csv(raw)
        est=montar_estacao_sace(registros,'SACE/SGB (automático)',
            codigo='75900000',nome='Itaqui',municipio='Itaqui',
            rio='RIO URUGUAI',inundacao_cm=830,latitude=-29.1175,longitude=-56.5544)
        diag.update({'automatico':True,'urlCSV':url,'registrosValidos':len(registros),
                     'ultimaMedicao':est['dataHoraMedicao'],'nivelCm':est['nivelCm'],
                     'horasDesdeMedicao':est['horasDesdeMedicao'],'dadoAntigo':est['dadoAntigo']})
        return est,diag
    except Exception as exc:
        diag['erro']=str(exc)[:250]
        diag['observacao']='Sem leitura válida do CSV SACE de Itaqui; nenhuma medição foi inventada.'
        return None,diag

def obter_itaqui_cache():
    with LOCK_ITAQUI:
        if CACHE_ITAQUI['data'] is None or time.time()-CACHE_ITAQUI['time']>=300:
            est,diag=consultar_sace_itaqui()
            CACHE_ITAQUI.update(time=time.time(),data={'estacao':est,'diagnostico':diag})
        return CACHE_ITAQUI['data']

# Histórico local da estação de referência Estrela/Lajeado.
# Calcula a variação real em aproximadamente uma hora, sem assumir que
# taxaMudancaValor (que pode representar 24h) é uma taxa horária.
HIST_LAJEADO=ROOT/"historico_lajeado.json"
def atualizar_tendencia_lajeado(estacoes):
    candidatos=[e for e in estacoes if ("estrela" in normal(e.get("nomeEstacao"))
               or normal(e.get("municipio"))=="estrela")
               and "taquari" in normal(e.get("rio")) and e.get("nivelMetros") is not None]
    if not candidatos:return
    est=max(candidatos,key=lambda e:str(e.get("dataHoraMedicao") or ""))
    codigo=str(est.get("codigoEstacao") or est.get("nomeEstacao"))
    medicao=str(est.get("dataHoraMedicao") or "")
    try:nivel=float(est["nivelMetros"])
    except (TypeError,ValueError):return
    if not medicao or not (0 <= nivel <= 50):return
    try:
        historico=json.loads(HIST_LAJEADO.read_text(encoding="utf-8"))
        if not isinstance(historico,list):historico=[]
    except (OSError,ValueError):historico=[]
    agora=time.time()
    historico=[x for x in historico if x.get("codigo")==codigo
              and 0<=agora-float(x.get("coletado",0))<=172800]
    if not any(x.get("medicao")==medicao for x in historico):
        historico.append({"codigo":codigo,"medicao":medicao,"nivel":nivel,"coletado":agora})
        try:HIST_LAJEADO.write_text(json.dumps(historico,ensure_ascii=False),encoding="utf-8")
        except OSError:pass
    # Apenas medições distintas da mesma estação, coletadas 45-75 min antes.
    anteriores=[x for x in historico if x["medicao"]!=medicao
                and 2700<=agora-x["coletado"]<=4500]
    if not anteriores:return
    ref=min(anteriores,key=lambda x:abs(agora-x["coletado"]-3600))
    delta=round((nivel-float(ref["nivel"]))*100,1)
    if abs(delta)<0.05:descricao="Estável na última hora"
    else:
        verbo="Desceu" if delta<0 else "Subiu"
        valor=abs(delta)
        num=("%g"%valor).replace(".",",")
        descricao=f"{verbo} {num} cm na última hora"
    est["taxaMudanca"]=descricao
    est["taxaMudancaValor"]=delta
    est["tendenciaPeriodo"]="aproximadamente 1 hora"
    est["tendenciaFonte"]="Histórico local das medições ClimaRS da estação Estrela"

def consultar():
    dados={"consultadoEm":datetime.now().astimezone().isoformat(),"fonte":"ClimaRS / ANA","estacoes":[],"erros":[],"municipiosConsultados":[]}
    try:
        municipios=getjson(IBGE)
        codigos={**CODIGOS_FIXOS, **{normal(m["nome"]):str(m["id"]) for m in municipios}}
    except Exception as e:
        dados["erros"].append("Não foi possível obter códigos IBGE: "+str(e))
        codigos=CODIGOS_FIXOS.copy()
    vistos=set()
    for nome in MUNICIPIOS:
        codigo=codigos.get(normal(nome))
        if not codigo:
            dados["erros"].append("Município não localizado no IBGE: "+nome)
            continue
        try:
            resultado=getjson(BASE+codigo)
            if not isinstance(resultado,list):
                raise ValueError("Resposta não é lista de estações")
            dados["municipiosConsultados"].append(nome)
            for item in resultado:
                if not isinstance(item,dict):continue
                chave=str(item.get("codigoEstacao") or "") or (str(item.get("nomeEstacao"))+str(item.get("municipio")))
                if chave not in vistos:
                    vistos.add(chave)
                    dados["estacoes"].append(item)
        except Exception as e:
            dados["erros"].append(nome+": "+str(e))
    atualizar_tendencia_lajeado(dados['estacoes'])
    dados['estacoes']=[e for e in dados['estacoes'] if not (normal(e.get('municipio'))=='sao borja' and str(e.get('codigoEstacao'))!='75780000')]
    # Fonte EXCLUSIVA de São Borja: SACE/SGB, estação Passo São Borja (ANA 75780000).
    # Não usar ClimaRS, ANA legado, Garruchos ou arquivo CSV local como substitutos.
    dados['estacoes']=[e for e in dados['estacoes'] if str(e.get('codigoEstacao'))!='75780000']
    try:
        with LOCK_SAO_BORJA:
            if CACHE_SAO_BORJA['data'] is None or time.time()-CACHE_SAO_BORJA['time'] >= 300:
                est,diag=consultar_sace_sao_borja()
                CACHE_SAO_BORJA.update(time=time.time(),data={'estacao':est,'diagnostico':diag})
            else:
                est=CACHE_SAO_BORJA['data']['estacao'];diag=CACHE_SAO_BORJA['data']['diagnostico']
        dados['saceDiagnostico']=diag
        if est:
            dados['estacoes'].append(est)
        else:
            dados['erros'].append('São Borja: SACE indisponível; nenhuma fonte alternativa será usada.')
    except Exception as e:
        dados['saceDiagnostico']={'automatico':False,'fonte':'SACE/SGB',
                                  'estacao':'Passo São Borja','erro':str(e)}
        dados['erros'].append('São Borja: falha na consulta SACE; sem leitura.')
    # Itaqui: consulta exclusiva ao SACE 75900000; não substituir por estação vizinha.
    dados['estacoes']=[e for e in dados['estacoes'] if normal(e.get('municipio'))!='itaqui' and str(e.get('codigoEstacao'))!='75900000']
    resultado_itaqui=obter_itaqui_cache()
    dados['saceItaquiDiagnostico']=resultado_itaqui['diagnostico']
    if resultado_itaqui['estacao']:
        dados['estacoes'].append(resultado_itaqui['estacao'])
    else:
        dados['erros'].append('Itaqui: SACE indisponível; sem medição confirmada.')
    # Rio Pardo: escolher a medição MAIS RECENTE da mesma estação ANA 85900000.
    # Não substituir por Praia dos Ingazeiros ou por outra régua com zero diferente.
    est_rp,diag_rp=consultar_sace_rio_pardo()
    candidatos_rp=[e for e in dados['estacoes']
                   if str(e.get('codigoEstacao') or '').strip()=='85900000']
    if est_rp:
        candidatos_rp.append(est_rp)
    # Se a leitura SACE estiver antiga, consultar também a telemetria ANA legado.
    # A API pode não fornecer dados recentes; nunca simular atualização.
    try:
        est_ana,diag_ana=ana_por_codigo('Rio Pardo','85900000')
        dados.setdefault('anaDiagnostico',[]).append(diag_ana)
        if est_ana:
            candidatos_rp.append(est_ana)
    except Exception as exc:
        dados['erros'].append('Rio Pardo: ANA legado: '+str(exc)[:200])
    def _data_rp(e):
        valor=str(e.get('dataHoraMedicao') or '').strip()
        for formato in ('%d/%m/%Y %H:%M:%S','%d/%m/%Y %H:%M','%Y-%m-%dT%H:%M:%S'):
            try:
                return datetime.strptime(valor[:19],formato).replace(tzinfo=timezone(timedelta(hours=-3)))
            except ValueError:
                pass
        return datetime.min.replace(tzinfo=timezone.utc)
    dados['estacoes']=[e for e in dados['estacoes']
                       if str(e.get('codigoEstacao') or '').strip()!='85900000']
    if candidatos_rp:
        escolhido=max(candidatos_rp,key=_data_rp)
        idade_h=(datetime.now(timezone(timedelta(hours=-3)))-_data_rp(escolhido)).total_seconds()/3600
        escolhido=dict(escolhido)
        escolhido['horasDesdeMedicao']=round(idade_h,1)
        escolhido['dadoAntigo']=idade_h>=12
        escolhido['confiavel']=0<=idade_h<12
        if idade_h>=12:
            escolhido['status']='DADO_ANTIGO'
            escolhido['statusLabel']='Última medição disponível (antiga)'
            escolhido['taxaMudanca']=None
            escolhido['taxaMudancaValor']=None
        dados['estacoes'].append(escolhido)
        diag_rp['fonteSelecionada']=escolhido.get('fonte')
        diag_rp['ultimaMedicaoSelecionada']=escolhido.get('dataHoraMedicao')
        diag_rp['dadoAntigoSelecionado']=idade_h>=12
        if idade_h>=12:
            dados['erros'].append('Rio Pardo: a estação 85900000 não forneceu leitura recente; exibida a última medição real, com data original.')
    else:
        dados['erros'].append('Rio Pardo: sem medições confirmadas da estação 85900000.')
    dados['saceRioPardoDiagnostico']=diag_rp
    # Arroio do Meio: estação DCRS-00104 da Defesa Civil RS (Rio Taquari).
    # A fonte ClimaRS/ANA 86878700 não vinha fornecendo leitura; a estação
    # estadual tem código distinto, portanto a identidade é mostrada explicitamente.
    dados['estacoes']=[e for e in dados['estacoes']
        if normal(e.get('municipio'))!='arroio do meio' and
           str(e.get('codigoEstacao') or '').strip()!='86878700']
    est_am, diag_am = consultar_arroio_dcrs()
    dados['arroioDoMeioDiagnostico']=diag_am
    if est_am:
        dados['estacoes'].append(est_am)
    else:
        dados['erros'].append('Arroio do Meio: nenhuma medição real disponível no histórico ou cache.')
    # Santa Maria: consulta direta da estação DCRS-00027.
    dados['estacoes']=[e for e in dados['estacoes'] if normal(e.get('municipio'))!='santa maria']
    est_sm,diag_sm=consultar_santa_maria_dcrs()
    dados['santaMariaDiagnostico']=diag_sm
    if est_sm:dados['estacoes'].append(est_sm)
    else:dados['erros'].append('Santa Maria: estação DCRS-00027 sem leitura confirmada.')
    return dados

# Consulta pública oficial, sem credenciais HidroWebService da ANA.
# O endpoint só permite a consulta Historic no formato documentado.
DCRS_GRAPHQL='https://redehidrometeorologica.defesacivil.rs.gov.br/graphql'
ARROIO_ULTIMA_LEITURA=ROOT/'arroio_ultima_leitura.json'

def _ler_ultima_arroio():
    try:
        dado=json.loads(ARROIO_ULTIMA_LEITURA.read_text(encoding='utf-8'))
        est=dado.get('estacao')
        if isinstance(est,dict) and est.get('codigoFonte')=='DCRS-00104' and isinstance(est.get('nivelMetros'),(int,float)):
            return est
    except (OSError,ValueError,TypeError,AttributeError):
        pass
    return None

def _salvar_ultima_arroio(est):
    try:
        temp=ARROIO_ULTIMA_LEITURA.with_suffix('.tmp')
        temp.write_text(json.dumps({'estacao':est},ensure_ascii=False),encoding='utf-8')
        temp.replace(ARROIO_ULTIMA_LEITURA)
    except OSError:
        pass  # Render Free pode apagar o cache ao reiniciar

DCRS_HISTORIC_QUERY="""query Historic($stationCode: String!, $startDate: String!, $endDate: String!, $interval: QueryInterval) {
  historic(
    system: Qualle_Hidrometeorologia
    client: "casa-militar-defesa-civil-rs"
    stationCode: $stationCode
    startDate: $startDate
    endDate: $endDate
    interval: $interval
    opts: { ordenacao: ASC }
  )
}"""


def consultar_santa_maria_dcrs():
    """Busca a última leitura real DCRS-00027, sem simular valor atual."""
    diag={'fonte':'Defesa Civil RS / Rede Hidrometeorológica',
          'estacao':'DCRS-00027','municipio':'Santa Maria',
          'url':'https://redehidrometeorologica.defesacivil.rs.gov.br/Estacao/DCRS-00027',
          'automatico':False}
    tz=timezone(timedelta(hours=-3)); agora=datetime.now(tz)
    try:
        payload=json.dumps({'query':DCRS_HISTORIC_QUERY,'variables':{
            'stationCode':'DCRS-00027',
            'startDate':(agora-timedelta(days=30)).strftime('%Y-%m-%d %H:%M:%S'),
            'endDate':agora.strftime('%Y-%m-%d %H:%M:%S'),
            'interval':'HOUR_1'}}).encode('utf-8')
        req=urllib.request.Request(DCRS_GRAPHQL,data=payload,headers={
            'Content-Type':'application/json','Accept':'application/json',
            'User-Agent':'Dashboard-Hidrologico-3DE/1.0'},method='POST')
        with urllib.request.urlopen(req,timeout=22) as r:
            resposta=json.loads(r.read(3_000_000).decode('utf-8'))
        if resposta.get('errors'):raise ValueError(str(resposta['errors'])[:250])
        items=(((resposta.get('data') or {}).get('historic') or {}).get('items') or [])
        leituras=[]
        for item in items:
            if str(item.get('codigo') or 'DCRS-00027')!='DCRS-00027':continue
            valor=item.get('rio_nivel')
            if isinstance(valor,bool) or not isinstance(valor,(int,float)) or not math.isfinite(valor) or not 0<=valor<=200:continue
            try:
                dt=datetime.fromisoformat(str(item['ts']).replace('Z','+00:00'))
                if dt.tzinfo is None:dt=dt.replace(tzinfo=tz)
                dt=dt.astimezone(tz)
            except (ValueError,TypeError,KeyError):continue
            if -300<=(agora-dt).total_seconds()<=30*86400:
                leituras.append((dt,float(valor),item.get('rio_variacao')))
        if not leituras:raise ValueError('Sem leituras válidas para DCRS-00027')
        leituras.sort(key=lambda x:x[0]); dt,nivel,variacao=leituras[-1]
        idade=max(0,(agora-dt).total_seconds()/3600)
        delta=None
        if isinstance(variacao,(int,float)) and not isinstance(variacao,bool) and math.isfinite(variacao):
            delta=round(variacao*100,1)
        if delta is None:
            anteriores=[(abs((dt-d).total_seconds()-3600),v) for d,v,_ in leituras[:-1]
                        if 1800<=(dt-d).total_seconds()<=5400]
            if anteriores:delta=round((nivel-min(anteriores)[1])*100,1)
        tendencia=None
        if delta is not None:
            num=('%g'%abs(delta)).replace('.',',')
            tendencia=('Subiu '+num+' cm na última hora' if delta>0 else
                       'Desceu '+num+' cm na última hora' if delta<0 else
                       'Estável na última hora')
        est={'codigoEstacao':'DCRS-00027','codigoFonte':'DCRS-00027',
             'nomeEstacao':'Santa Maria (DCRS-00027)',
             'municipio':'Santa Maria','rio':'ARROIO CADENA',
             'nivelCm':round(nivel*100,1),'nivelMetros':nivel,
             'dataHoraMedicao':dt.strftime('%d/%m/%Y %H:%M:%S'),
             'dataHoraShort':dt.strftime('%d/%m %H:%M'),
             'confiavel':idade<12,'dadoAntigo':idade>=12,
             'status':'DADO_ANTIGO' if idade>=12 else 'MEDICAO',
             'taxaMudanca':tendencia if idade<12 else None,
             'taxaMudancaValor':delta if idade<12 else None,
             'fonte':'Defesa Civil RS (DCRS-00027)',
             'horasDesdeMedicao':round(idade,1)}
        diag.update(automatico=True,ultimaMedicao=est['dataHoraMedicao'],
                    nivelMetros=nivel,registrosValidos=len(leituras),
                    dadoAntigo=idade>=12,
                    observacao='Verificar compatibilidade do referencial altimétrico com as cotas 68,90/69,00 m.')
        return est,diag
    except Exception as exc:
        diag['erro']=str(exc)[:300]
        return None,diag

def consultar_arroio_dcrs():
    diag={'fonte':'Defesa Civil RS / Rede Hidrometeorológica',
          'estacao':'DCRS-00104','municipio':'Arroio do Meio',
          'codigoANAAnterior':'86878700','automatico':False,
          'url':DCRS_GRAPHQL}
    try:
        tz=timezone(timedelta(hours=-3))
        agora=datetime.now(tz)
        inicio=agora-timedelta(days=30)
        payload=json.dumps({'query':DCRS_HISTORIC_QUERY,'variables':{
            'stationCode':'DCRS-00104',
            'startDate':inicio.strftime('%Y-%m-%d %H:%M:%S'),
            'endDate':agora.strftime('%Y-%m-%d %H:%M:%S'),
            'interval':'HOUR_1'}}).encode('utf-8')
        req=urllib.request.Request(DCRS_GRAPHQL,data=payload,headers={
            'Content-Type':'application/json','Accept':'application/json',
            'User-Agent':'Dashboard-Hidrologico-3DE/1.0'},method='POST')
        with urllib.request.urlopen(req,timeout=22) as r:
            resposta=json.loads(r.read(3_000_000).decode('utf-8'))
        if resposta.get('errors'):
            raise ValueError(str(resposta['errors'])[:250])
        historico=((resposta.get('data') or {}).get('historic') or {})
        items=historico.get('items') or []
        leituras=[]
        for item in items:
            if str(item.get('codigo') or 'DCRS-00104')!='DCRS-00104':continue
            valor=item.get('rio_nivel')
            if isinstance(valor,bool) or not isinstance(valor,(int,float)) or not math.isfinite(valor) or not 0<=valor<=100:continue
            try:
                instante=datetime.fromisoformat(str(item['ts']).replace('Z','+00:00'))
                if instante.tzinfo is None:instante=instante.replace(tzinfo=tz)
                instante=instante.astimezone(tz)
            except (ValueError,TypeError):continue
            if -300<=(agora-instante).total_seconds()<=30*86400:
                leituras.append((instante,float(valor),item.get('rio_variacao')))
        if not leituras:raise ValueError('Nenhuma medição válida na resposta da estação DCRS-00104')
        leituras.sort(key=lambda x:x[0]); instante,nivel,variacao=leituras[-1]
        idade=(agora-instante).total_seconds()/3600
        # A última leitura é mantida, mas identificada como antiga quando >12h.
        delta=None
        if isinstance(variacao,(int,float)) and not isinstance(variacao,bool) and math.isfinite(variacao):
            delta=round(variacao*100,1)
        if delta is None:
            anteriores=[(abs((instante-d).total_seconds()-3600),v) for d,v,_ in leituras[:-1]
                        if 1800<=(instante-d).total_seconds()<=5400]
            if anteriores:delta=round((nivel-min(anteriores)[1])*100,1)
        tendencia=None
        if delta is not None:
            num=('%g'%abs(delta)).replace('.',',')
            tendencia=('Subiu '+num+' cm na última hora' if delta>0 else
                       'Desceu '+num+' cm na última hora' if delta<0 else
                       'Estável na última hora')
        # Cota municipal de 24,50 m: só pode ser aplicada se o referencial
        # altimétrico da estação DCRS for confirmado como compatível.
        est={'codigoEstacao':'86878700','codigoFonte':'DCRS-00104',
             'nomeEstacao':'Arroio do Meio (DCRS-00104)',
             'municipio':'Arroio do Meio','rio':'RIO TAQUARI',
             'nivelCm':round(nivel*100,1),'nivelMetros':nivel,
             'dataHoraMedicao':instante.strftime('%d/%m/%Y %H:%M:%S'),
             'dataHoraShort':instante.strftime('%d/%m %H:%M'),
             'confiavel':True,'status':'SEM_CLASSIFICACAO',
             'statusLabel':'Leitura confirmada; referencial da cota em validação',
             'taxaMudanca':tendencia,'taxaMudancaValor':delta,
             'fonte':'Defesa Civil RS (DCRS-00104)',
             'latitude':-29.402,'longitude':-51.944,
             'horasDesdeMedicao':round(idade,1)}
        diag.update(automatico=True,ultimaMedicao=est['dataHoraMedicao'],
                    nivelMetros=nivel,registrosValidos=len(leituras),
                    observacao='Cota municipal de 24,50 m não aplicada à estação DCRS até validação de referencial.')
        _salvar_ultima_arroio(est)
        return est,diag
    except Exception as exc:
        diag['erro']=str(exc)[:300]
        anterior=_ler_ultima_arroio()
        if anterior:
            anterior=dict(anterior)
            anterior['confiavel']=False
            anterior['dadoAntigo']=True
            anterior['statusLabel']='Última medição disponível (cache local; pode estar antiga)'
            anterior['taxaMudanca']=None
            anterior['taxaMudancaValor']=None
            diag['cacheAnterior']=True
            diag['ultimaMedicao']=anterior.get('dataHoraMedicao')
            diag['observacao']='Fonte indisponível: exibindo a última medição real salva, não uma leitura atual.'
            return anterior,diag
        diag['observacao']='Nenhuma medição real encontrada no histórico consultado ou cache local.'
        return None,diag

def ana_por_codigo(nome,codigo):
    agora=datetime.now().astimezone()
    ini=(agora.date()-timedelta(days=14)).strftime("%d/%m/%Y")
    fim=agora.date().strftime("%d/%m/%Y")
    q=urllib.parse.urlencode({"CodEstacao":codigo,"DataInicio":ini,"DataFim":fim})
    url="https://www.ana.gov.br/telemetria1ws/ServiceANA.asmx/DadosHidrometeorologicos?"+q
    req=urllib.request.Request(url,headers={"User-Agent":"Mozilla/5.0","Accept":"text/xml,application/xml"})
    with urllib.request.urlopen(req,timeout=18) as r:raw=r.read()
    root=ET.fromstring(raw)
    # Procura registros com DataHora e Nivel no mesmo elemento (evita misturar linhas).
    registros=[]
    for el in root.iter():
        filhos={x.tag.split("}")[-1].lower():(x.text or "").strip() for x in el}
        if "datahora" not in filhos or "nivel" not in filhos:continue
        if filhos.get("codestacao",codigo)!=codigo:continue
        try:
            instante=datetime.fromisoformat(filhos["datahora"].strip().replace(" ","T",1))
            nivel=float(filhos["nivel"].replace(",","."))
            if instante.tzinfo is None:instante=instante.replace(tzinfo=timezone(timedelta(hours=-3)))
            if 0<=nivel<=100000:registros.append((instante,nivel))
        except (ValueError,TypeError):continue
    registros.sort(key=lambda x:x[0],reverse=True)
    diag={"municipio":nome,"codigo":codigo,"registros":len(registros),"fonte":"ANA telemetria legado"}
    if not registros:return None,diag
    instante,nivel=registros[0]
    horas=(agora-instante).total_seconds()/3600
    diag.update({"ultimaMedicao":instante.isoformat(),"horasDesdeMedicao":round(horas,1),"nivelBrutoCm":nivel})
    # Segurança: não publicar valores antigos como leitura operacional atual.
    if horas<0 or horas>24:
        diag["observacao"]="Dado antigo ou horário inconsistente; não publicado como atual"
        return None,diag
    if nome=='Arroio do Meio':
        # Cota em centímetros; apenas estação 86878700, com horário validado.
        if horas>12:
            diag['observacao']='Leitura superior a 12 horas; não publicada como atual'
            return None,diag
        return {'codigoEstacao':codigo,'nomeEstacao':'Arroio do Meio',
            'municipio':nome,'rio':'RIO TAQUARI','nivelCm':nivel,
            'nivelMetros':nivel/100,'dataHoraMedicao':instante.strftime('%d/%m/%Y %H:%M:%S'),
            'dataHoraShort':instante.strftime('%d/%m %H:%M'),'confiavel':True,
            'status':'INUNDACAO' if nivel>=2450 else 'NORMAL',
            'statusLabel':'Inundação' if nivel>=2450 else 'Abaixo da inundação',
            'taxaMudanca':None,'taxaMudancaValor':None,
            'fonte':'ANA telemetria (legado)','horasDesdeMedicao':round(horas,1)},diag
    # Nível ANA é expresso em centímetros na API de telemetria.
    return {"codigoEstacao":codigo,"nomeEstacao":nome,"municipio":nome,
      "rio":{"São Borja":"RIO URUGUAI","Rio Pardo":"RIO JACUÍ","São Sepé":"RIO SÃO SEPÉ"}[nome],
      "nivelCm":nivel,"nivelMetros":nivel/100,"dataHoraMedicao":instante.strftime("%d/%m/%Y %H:%M:%S"),
      "dataHoraShort":instante.strftime("%d/%m %H:%M"),"confiavel":False,"status":"SEM_CLASSIFICACAO",
      "statusLabel":"Sem classificação (ANA)","taxaMudanca":None,"taxaMudancaValor":None,
      "fonte":"ANA legado","horasDesdeMedicao":round(horas,1)},diag


# Previsão de 7 dias: todos os 13 municípios representados nos cartões do painel.
# Barra do Fão é uma localidade, representada por coordenadas da região da estação.
PONTOS_PREVISAO=[
    ("São Borja",-28.660,-56.004),
    ("Itaqui",-29.125,-56.553),
    ("Uruguaiana",-29.760,-57.087),
    ("Manoel Viana",-29.587,-55.483),
    ("Alegrete",-29.783,-55.792),
    ("Quaraí",-30.385,-56.451),
    ("Rosário do Sul",-30.258,-54.914),
    ("Cachoeira do Sul",-30.039,-52.894),
    ("Lajeado",-29.467,-51.961),
    ("Rio Pardo",-29.990,-52.378),
    ("Arroio do Meio",-29.402,-51.944),
    ("São Sepé",-30.164,-53.565),
    ("Santa Maria",-29.6842,-53.8069),
]
PREVISAO_CACHE={"time":0,"data":None,"ultima_valida":None}
PREVISAO_LOCK=threading.Lock()
PREVISAO_CACHE_ARQUIVO=ROOT/"previsao_cache.json"

def _ler_previsao_cache():
    try:
        dado=json.loads(PREVISAO_CACHE_ARQUIVO.read_text(encoding="utf-8"))
        if dado.get("disponivel") and dado.get("pontos"):
            return dado
    except (OSError,ValueError,TypeError):
        pass
    return None

def _salvar_previsao_cache(dado):
    try:
        PREVISAO_CACHE_ARQUIVO.write_text(json.dumps(dado,ensure_ascii=False),encoding="utf-8")
    except OSError:
        pass  # Filesystem do Render Free não é persistente.

def _acumulados_por_dia(horas_unicas, datas):
    """Soma apenas horas efetivamente fornecidas; nunca inventa chuva zero."""
    saida=[]
    for dia in datas:
        valores=[v for hora,v in horas_unicas.items() if hora[:10]==dia]
        saida.append({"data":dia,
                      "mm":round(sum(valores),1) if valores else None,
                      "horasValidas":len(valores),
                      "completo":len(valores)>=24})
    return saida


def _previsao_met_norway(nome, lat, lon, datas):
    """MET Norway: combina intervalos de 1h, 6h e 12h sem sobreposição.

    O Locationforecast fornece horas individuais no início do horizonte e
    intervalos mais longos nos dias seguintes. Somar somente next_1_hours
    perde a maior parte da previsão. Cada intervalo é usado uma única vez.
    """
    params=urllib.parse.urlencode({"lat":f"{lat:.3f}","lon":f"{lon:.3f}"})
    url="https://api.met.no/weatherapi/locationforecast/2.0/compact?"+params
    req=urllib.request.Request(url,headers={
        "User-Agent":"MonitoramentoHidrologico3DE/1.0 (https://github.com/gomestopografia-dot/monitoramento-hidrologico-3de)",
        "Accept":"application/json"})
    with urllib.request.urlopen(req,timeout=18) as r:
        dados=json.loads(r.read(2_000_000).decode("utf-8"))
    series=dados.get("properties",{}).get("timeseries",[])
    tz_br=timezone(timedelta(hours=-3))
    # Indexar todos os intervalos existentes; preferir 1h, depois 6h, depois 12h.
    # Nunca repartir uma quantidade de 6/12h artificialmente em horas.
    candidatos=[]
    for item in series:
        try:
            inicio=datetime.fromisoformat(item["time"].replace("Z","+00:00")).astimezone(tz_br)
            for duracao in (1,6,12):
                detalhe=item.get("data",{}).get(f"next_{duracao}_hours",{}).get("details",{})
                valor=detalhe.get("precipitation_amount")
                if isinstance(valor,bool) or not isinstance(valor,(int,float)) or not math.isfinite(valor) or not 0<=valor<=1000:
                    continue
                candidatos.append((inicio,inicio+timedelta(hours=duracao),float(valor),duracao))
        except (KeyError,TypeError,ValueError,AttributeError):
            continue
    if not candidatos:raise ValueError("Sem intervalos de precipitação válidos")
    inicio_janela=datetime.fromisoformat(datas[0]).replace(tzinfo=tz_br)
    fim_janela=datetime.fromisoformat(datas[-1]).replace(tzinfo=tz_br)+timedelta(days=1)
    # Intervalos de menor duração têm prioridade, sem duplicar o mesmo período.
    candidatos.sort(key=lambda x:(x[3],x[0]))
    ocupadas=set();selecionados=[]
    for inicio,fim,valor,duracao in candidatos:
        if inicio<inicio_janela or fim>fim_janela:continue
        slots=[inicio+timedelta(hours=i) for i in range(duracao)]
        if any(slot in ocupadas for slot in slots):continue
        selecionados.append((inicio,fim,valor,duracao))
        ocupadas.update(slots)
    if not selecionados:raise ValueError("Sem intervalos dentro dos sete dias")
    chuva_diaria=[]
    for dia in datas:
        inicio_dia=datetime.fromisoformat(dia).replace(tzinfo=tz_br)
        fim_dia=inicio_dia+timedelta(days=1)
        partes=[v for ini,fim,v,d in selecionados if ini>=inicio_dia and fim<=fim_dia]
        # Não dividir intervalos que cruzem a meia-noite: esses valores
        # não podem ser atribuídos com precisão a um dia específico.
        horas=sum(d for ini,fim,v,d in selecionados if ini>=inicio_dia and fim<=fim_dia)
        chuva_diaria.append({"data":dia,"mm":round(sum(partes),1) if partes else None,
                            "horasValidas":horas,"completo":horas>=24})
    # Picos de 50 mm/h: exclusivamente intervalos de 1 hora.
    individuais=[(ini,v) for ini,fim,v,d in selecionados if d==1]
    pico,maior=max(individuais,key=lambda x:x[1]) if individuais else (None,0.0)
    return {"municipio":nome,"maximoHorarioMmH":round(maior,1),
            "horaPico":pico.strftime("%Y-%m-%dT%H:%M") if pico else None,
            "acumuladoPrevistoMm":round(sum(v for _,_,v,_ in selecionados),1),
            "acumuladoCompleto":all(d["completo"] for d in chuva_diaria),
            "fonte":"MET Norway (1h/6h/12h)","horasValidas":len(ocupadas),
            "chuvaDiaria":chuva_diaria}


def consultar_previsao():
    """Open-Meteo agrupada; MET Norway somente para localidades sem dados."""
    from concurrent.futures import ThreadPoolExecutor, as_completed
    hoje=datetime.now(timezone(timedelta(hours=-3))).date()
    datas=[(hoje+timedelta(days=i)).isoformat() for i in range(7)]
    nomes=[p[0] for p in PONTOS_PREVISAO]
    params=urllib.parse.urlencode({
        "latitude":",".join(str(p[1]) for p in PONTOS_PREVISAO),
        "longitude":",".join(str(p[2]) for p in PONTOS_PREVISAO),
        "hourly":"precipitation", "timezone":"America/Sao_Paulo",
        "forecast_days":7, "precipitation_unit":"mm"})
    url="https://api.open-meteo.com/v1/forecast?"+params
    pontos=[];erros=[]
    try:
        resposta=getjson(url,timeout=25)
        if isinstance(resposta,dict):resposta=[resposta]
        if not isinstance(resposta,list) or len(resposta)!=len(nomes):
            raise ValueError("Formato de resposta Open-Meteo inesperado")
        for nome,estacao in zip(nomes,resposta):
            try:
                if not isinstance(estacao,dict) or estacao.get("error"):
                    raise ValueError(str(estacao.get("reason","Resposta inválida")) if isinstance(estacao,dict) else "Resposta inválida")
                horario=estacao.get("hourly") or {}
                horas=horario.get("time") or []
                valores=horario.get("precipitation") or []
                if len(horas)!=len(valores) or not horas:raise ValueError("Série horária incompleta")
                registros=[(hora,float(valor)) for hora,valor in zip(horas,valores)
                    if isinstance(hora,str) and hora[:10] in datas
                    and isinstance(valor,(int,float)) and not isinstance(valor,bool)
                    and math.isfinite(valor) and 0<=valor<=1000]
                if not registros:raise ValueError("Nenhuma hora com previsão válida")
                hora_max,maior=max(registros,key=lambda x:x[1])
                horas_unicas={hora:valor for hora,valor in registros}
                pontos.append({"municipio":nome,"maximoHorarioMmH":round(maior,1),
                               "horaPico":hora_max,"fonte":"Open-Meteo","horasValidas":len(horas_unicas),
                               "acumuladoPrevistoMm":round(sum(horas_unicas.values()),1),
                               "acumuladoCompleto":all(d["completo"] for d in _acumulados_por_dia(horas_unicas,datas)),
                               "chuvaDiaria":_acumulados_por_dia(horas_unicas,datas)})
            except (ValueError,TypeError,AttributeError) as exc:
                erros.append({"municipio":nome,"fonte":"Open-Meteo","erro":str(exc)[:250]})
    except urllib.error.HTTPError as exc:
        erros.append({"fonte":"Open-Meteo","erro":f"HTTP {exc.code}: {exc.reason}"})
    except Exception as exc:
        erros.append({"fonte":"Open-Meteo","erro":str(exc)[:250]})

    # Não repetir a Open-Meteo em caso de 429. Fonte alternativa independente.
    faltantes=[p for p in PONTOS_PREVISAO if p[0] not in {x["municipio"] for x in pontos}]
    if faltantes:
        with ThreadPoolExecutor(max_workers=3) as pool:
            tarefas={pool.submit(_previsao_met_norway,nome,lat,lon,datas):nome
                     for nome,lat,lon in faltantes}
            for tarefa in as_completed(tarefas):
                try:pontos.append(tarefa.result())
                except Exception as exc:
                    erros.append({"municipio":tarefas[tarefa],"fonte":"MET Norway","erro":str(exc)[:250]})
    # Ordem estável e resultado transparente quanto à cobertura.
    pontos.sort(key=lambda p:nomes.index(p["municipio"]))
    maior=max(pontos,key=lambda p:p["maximoHorarioMmH"]) if pontos else None
    acima=[p for p in pontos if p["maximoHorarioMmH"]>50.0]
    fontes=sorted({p["fonte"] for p in pontos})
    # Média municipal dos acumulados de sete dias, somente para séries completas.
    completos=[p for p in pontos if p.get("acumuladoCompleto")]
    # Não apresentar a previsão parcial da MET Norway como acumulado de sete dias.
    # Quando não houver séries completas, comparar apenas municípios com a mesma
    # quantidade de horas válidas; períodos de tamanhos distintos não são comparáveis.
    if completos:
        base_media=completos
        media_parcial=False
    else:
        grupos={}
        for p in pontos:
            horas=p.get("horasValidas",0)
            if horas and isinstance(p.get("acumuladoPrevistoMm"),(int,float)):
                grupos.setdefault(horas,[]).append(p)
        base_media=max(grupos.values(),key=lambda grupo:(len(grupo),grupo[0]["horasValidas"])) if grupos else []
        media_parcial=bool(base_media)
    media_semanal=round(sum(p["acumuladoPrevistoMm"] for p in base_media)/len(base_media),1) if base_media else None
    return {"mediaAcumuladaMunicipiosMm":media_semanal,
        "mediaParcial":media_parcial,
        "horasCoberturaMedia":base_media[0].get("horasValidas") if base_media else 0,
        "municipiosMediaRecebidos":len(base_media),
        "municipiosMediaEsperados":len(PONTOS_PREVISAO),"disponivel":bool(pontos),"acima50":bool(acima),
        "maiorIntensidadeMmH":maior["maximoHorarioMmH"] if maior else None,
        "municipioMaiorIntensidade":maior["municipio"] if maior else None,
        "horaMaiorIntensidade":maior["horaPico"] if maior else None,
        "municipiosAcima50":acima,"pontos":pontos,"erros":erros,
        "pontosRecebidos":len(pontos),"pontosEsperados":len(PONTOS_PREVISAO),
        "coberturaCompleta":len(pontos)==len(PONTOS_PREVISAO),
        "seteDiasCompletos":len(pontos)==len(PONTOS_PREVISAO) and all(p.get("acumuladoCompleto") for p in pontos),
        "inicio":datas[0],"fim":datas[-1],
        "fonte":" / ".join(fontes) if fontes else "Open-Meteo / MET Norway (sem dados)",
        "metodologia":"Gatilho quando qualquer município tiver uma hora prevista com precipitação superior a 50,0 mm/h; não é probabilidade operacional. Fonte MET Norway combina intervalos de 1h, 6h e 12h sem sobreposição e pode ter cobertura inferior a 7 dias.",
        "erro":None,"atualizadoEm":datetime.now(timezone(timedelta(hours=-3))).isoformat()}

def obter_previsao_cache():
    hoje=datetime.now(timezone(timedelta(hours=-3))).date().isoformat()
    anterior=PREVISAO_CACHE["data"]
    # 120 minutos para previsão disponível; evita requisições repetidas e HTTP 429.
    ttl=7200 if anterior and anterior.get("disponivel") else 1800
    if anterior is None or anterior.get("inicio")!=hoje or not all("chuvaDiaria" in p for p in anterior.get("pontos",[])) or time.time()-PREVISAO_CACHE["time"]>=ttl:
        novo=consultar_previsao()
        if novo["disponivel"]:
            PREVISAO_CACHE["ultima_valida"]=novo
            _salvar_previsao_cache(novo)
            resultado=novo
        else:
            anterior_valido=PREVISAO_CACHE["ultima_valida"] or _ler_previsao_cache()
            # Apenas previsões do mesmo período; não reaproveitar previsão de outra semana.
            if anterior_valido and anterior_valido.get("inicio")==hoje and all("chuvaDiaria" in p for p in anterior_valido.get("pontos",[])):
                resultado=dict(anterior_valido)
                resultado["erros"]=novo["erros"]
                resultado["cacheAnterior"]=True
                resultado["aviso"]="Fonte indisponível: exibindo a última previsão válida, com horário original."
            else:
                resultado=novo
        PREVISAO_CACHE.update(data=resultado,time=time.time())
    return PREVISAO_CACHE["data"]


# Avisos oficiais do INMET: consulta independente e cache de 10 minutos.
INMET_AVISOS_URL="https://apiprevmet3.inmet.gov.br/avisos/ativos"
INMET_LOCK=threading.Lock()
INMET_CACHE={"time":0,"data":None}

def _codigos_rs(a):
    codigos=set()
    for key in ('geocodes','municipios','municipalities','codigosMunicipios'):
        val=a.get(key)
        if isinstance(val,str):val=re.split(r'[,;\s]+',val)
        if isinstance(val,list):
            for item in val:
                if isinstance(item,dict):
                    codigo=str(item.get('codigo') or item.get('codigo_ibge') or item.get('geocode') or item.get('id') or '')
                else:codigo=str(item)
                if re.fullmatch(r'43\d{5}',codigo):codigos.add(codigo)
    return sorted(codigos)

def _aviso_rs(a):
    if not isinstance(a,dict):return False
    if _codigos_rs(a):return True
    for key in ('uf','estado','siglaUf','sigla_uf'):
        if str(a.get(key) or '').strip().upper() in ('RS','RIO GRANDE DO SUL'):return True
    return False

def _poligono_aviso(a):
    # Aceitar apenas GeoJSON válido de Polygon/MultiPolygon publicado pela fonte.
    geo=a.get('poligono') or a.get('polygon') or a.get('geometry')
    if isinstance(geo,str):
        try:geo=json.loads(geo)
        except (ValueError,TypeError):return None
    if isinstance(geo,dict) and geo.get('type')=='Feature':geo=geo.get('geometry')
    if not isinstance(geo,dict) or geo.get('type') not in ('Polygon','MultiPolygon'):return None
    coords=geo.get('coordinates')
    if not isinstance(coords,list):return None
    # Limitar payload; não fabricar geometrias quando ausentes.
    if len(json.dumps(coords))>500000:return None
    return {'type':geo['type'],'coordinates':coords}

def _texto_aviso(a,*keys):
    for k in keys:
        v=a.get(k)
        if isinstance(v,(str,int,float)) and str(v).strip():return str(v).strip()[:1200]
    return ''

def obter_alertas_inmet():
    with INMET_LOCK:
        if INMET_CACHE['data'] is not None and time.time()-INMET_CACHE['time']<600:
            return INMET_CACHE['data']
        agora=datetime.now(timezone.utc).isoformat()
        try:
            dados=getjson(INMET_AVISOS_URL,timeout=18)
            if not isinstance(dados,(dict,list)):raise ValueError('Formato inesperado da API INMET')
            colecoes=([('vigente',dados)] if isinstance(dados,list) else [(k,dados.get(k,[])) for k in ('hoje','futuro')])
            avisos=[];vistos=set()
            for periodo,itens in colecoes:
                if not isinstance(itens,list):continue
                for a in itens:
                    if not _aviso_rs(a):continue
                    codigo=_texto_aviso(a,'id','id_aviso','codigo','identifier')
                    titulo=_texto_aviso(a,'descricao','titulo','evento','tipo','fenomeno')
                    chave=(codigo or titulo,_texto_aviso(a,'data_inicio','inicio'))
                    if chave in vistos:continue
                    vistos.add(chave)
                    municipios=a.get('municipios')
                    nomes=[]
                    if isinstance(municipios,list):
                        nomes=[str(x.get('nome') or x.get('municipio') or '')[:90] for x in municipios if isinstance(x,dict) and (str(x.get('uf') or '').upper()=='RS' or str(x.get('codigo') or x.get('id') or '').startswith('43'))]
                    avisos.append({'id':codigo,'titulo':titulo or 'Aviso meteorológico',
                        'severidade':_texto_aviso(a,'severidade','grau','nivel'),
                        'inicio':_texto_aviso(a,'data_inicio','inicio','start'),
                        'fim':_texto_aviso(a,'data_fim','fim','end'),
                        'riscos':_texto_aviso(a,'riscos','risco','risk'),
                        'instrucoes':_texto_aviso(a,'instrucoes','instrucoes_segurança','instruction'),
                        'municipios':nomes[:497],'codigosIbgeRS':_codigos_rs(a),
                        'granizo':('granizo' in normal(' '.join(str(a.get(k) or '') for k in ('riscos','descricao','titulo','evento','tipo','fenomeno')))),
                        'geometria':_poligono_aviso(a),'periodoFonte':periodo,
                        'url':('https://avisos.inmet.gov.br/'+codigo if codigo.isdigit() else 'https://avisos.inmet.gov.br/')})
            resultado={'fonte':'INMET','situacaoConsulta':'ok','consultadoEm':agora,
                'avisos':avisos,'total':len(avisos),'observacao':'Avisos para o RS com identificação explícita de UF ou código IBGE. Não é detecção de tornados.'}
        except Exception as exc:
            resultado={'fonte':'INMET','situacaoConsulta':'indisponivel','consultadoEm':agora,
                'avisos':[],'total':None,'erro':str(exc)[:240],
                'observacao':'Consulta indisponível; não interpretar como ausência de alertas.'}
        INMET_CACHE.update(time=time.time(),data=resultado)
        return resultado


# Proxy restrito para limites hidrográficos oficiais IEDE/RS.
# O navegador consulta este servidor, evitando bloqueios de origem cruzada (CORS).
IEDE_BACIAS_BASE='https://iede.rs.gov.br/server/rest/services/DRH/Bacias_Hidrograficas/MapServer'
BACIAS_CACHE={}
BACIAS_LOCK=threading.Lock()
BACIAS_REGIOES={'uruguai':'Uruguai','guaiba':'Guaíba','litoranea':'Litoral'}

def obter_bacia_geojson(chave):
    if chave not in BACIAS_REGIOES:
        return {'error':{'message':'Região inválida'}}
    # Prioriza limites oficiais baixados e validados localmente.
    # Não utiliza polígonos aproximados ou inventados.
    arquivo=ROOT/'bacias'/(chave+'.geojson')
    if arquivo.is_file():
        try:
            dados=json.loads(arquivo.read_text(encoding='utf-8-sig'))
            if (dados.get('type')=='FeatureCollection' and
                isinstance(dados.get('features'),list) and
                any(f.get('geometry') for f in dados['features'])):
                return dados
            return {'error':{'message':'GeoJSON local inválido ou sem geometrias: '+arquivo.name}}
        except Exception as exc:
            return {'error':{'message':'Erro lendo GeoJSON local: '+str(exc)[:180]}}

    with BACIAS_LOCK:
        entrada=BACIAS_CACHE.get(chave)
        if entrada and time.time()-entrada[0]<86400:return entrada[1]
    try:
        # A camada não é presumida: localizar o campo 'regiao' no catálogo oficial.
        catalogo=getjson(IEDE_BACIAS_BASE+'?f=pjson',timeout=18)
        camadas=catalogo.get('layers',[])
        if not camadas:raise ValueError('Catálogo IEDE sem camadas')
        falhas=[]
        for camada in camadas:
            ident=camada.get('id')
            if ident is None:continue
            try:
                meta=getjson(f'{IEDE_BACIAS_BASE}/{ident}?f=pjson',timeout=15)
                campos=meta.get('fields') or []
                campo=next((f['name'] for f in campos if normal(f.get('name'))=='regiao'),None)
                if not campo:continue
                valor=BACIAS_REGIOES[chave]
                # Usar a grafia registrada na fonte e incluir grafias sem acento.
                termos={'Uruguai':['Uruguai'],'Guaíba':['Guaíba','Guaiba'],'Litoral':['Litoral','Litorânea','Litoranea']}[valor]
                cond=' OR '.join(f"{campo} = '{t}'" for t in termos)
                params=urllib.parse.urlencode({'f':'geojson','where':f'({cond})','outFields':'*','returnGeometry':'true','outSR':'4326','geometryPrecision':'4','maxAllowableOffset':'0.004'})
                geo=getjson(f'{IEDE_BACIAS_BASE}/{ident}/query?{params}',timeout=35)
                if geo.get('type')=='FeatureCollection' and geo.get('features'):
                    features=[f for f in geo['features'] if f.get('geometry') and normal(f.get('properties',{}).get(campo)) in [normal(t) for t in termos]]
                    if features:
                        resultado={'type':'FeatureCollection','features':features}
                        with BACIAS_LOCK:BACIAS_CACHE[chave]=(time.time(),resultado)
                        return resultado
                falhas.append(f'Camada {ident}: sem polígonos correspondentes')
            except Exception as exc:falhas.append(f'Camada {ident}: {str(exc)[:100]}')
        raise ValueError('Não foi possível localizar os polígonos. '+'; '.join(falhas[:3]))
    except Exception as exc:
        return {'error':{'message':('Limites oficiais não disponíveis: '+str(exc))[:450]+'. Para funcionamento offline, adicione bacias/uruguai.geojson, bacias/guaiba.geojson e bacias/litoranea.geojson (dados oficiais).'}}

class Handler(SimpleHTTPRequestHandler):
    def __init__(self,*args,**kwargs):
        super().__init__(*args,directory=str(ROOT),**kwargs)
    def do_GET(self):
        if self.path.split('?')[0] == '/api/bacias':
            query=urllib.parse.parse_qs(urllib.parse.urlsplit(self.path).query)
            chave=query.get('regiao',[''])[0]
            data=obter_bacia_geojson(chave)
            body=json.dumps(data,ensure_ascii=False).encode('utf-8')
            self.send_response(200 if 'error' not in data else 503)
            self.send_header('Content-Type','application/json; charset=utf-8')
            self.send_header('Cache-Control','no-store')
            self.send_header('Content-Length',str(len(body)))
            self.end_headers();self.wfile.write(body)
            return
        if self.path.split("?")[0] == "/api/tempo-severo":
            data=obter_alertas_inmet()
            body=json.dumps(data,ensure_ascii=False).encode('utf-8')
            self.send_response(200);self.send_header('Content-Type','application/json; charset=utf-8')
            self.send_header('Cache-Control','no-store');self.send_header('Content-Length',str(len(body)))
            self.end_headers();self.wfile.write(body)
            return
        if self.path.split("?")[0] == "/api/previsao":
            with PREVISAO_LOCK:
                data=obter_previsao_cache()
            body=json.dumps(data,ensure_ascii=False).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type","application/json; charset=utf-8")
            self.send_header("Cache-Control","no-store")
            self.send_header("Content-Length",str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        if self.path.split("?")[0] == "/api/itaqui":
            data=obter_itaqui_cache()
            body=json.dumps(data,ensure_ascii=False).encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type','application/json; charset=utf-8')
            self.send_header('Cache-Control','no-store')
            self.send_header('Content-Length',str(len(body)))
            self.end_headers();self.wfile.write(body)
            return
        if self.path.split("?")[0] == "/api/sao-borja":
            # Consulta independente: não aguarda as dezenas de requisições ClimaRS.
            with LOCK_SAO_BORJA:
                if CACHE_SAO_BORJA['data'] is None or time.time()-CACHE_SAO_BORJA['time'] >= 300:
                    try:
                        est,diag=consultar_sace_sao_borja()
                    except Exception as exc:
                        est=None;diag={'automatico':False,'erro':repr(exc),'urlConfigurada':SACE_EXPORT_URL}
                    CACHE_SAO_BORJA.update(time=time.time(),data={'estacao':est,'diagnostico':diag})
                data=CACHE_SAO_BORJA['data']
            body=json.dumps(data,ensure_ascii=False).encode('utf-8')
            self.send_response(200);self.send_header('Content-Type','application/json; charset=utf-8')
            self.send_header('Cache-Control','no-store');self.send_header('Content-Length',str(len(body)))
            self.end_headers();self.wfile.write(body)
            return
        if self.path.split("?")[0] in ("/api/stations","/api/diagnostico"):
            with LOCK:
                if CACHE["data"] is None or time.time()-CACHE["time"]>300:
                    novo=consultar()
                    CACHE["data"]=novo
                    CACHE["time"]=time.time()
                data=CACHE["data"]
            body=json.dumps(data,ensure_ascii=False).encode("utf-8")
            self.send_response(200);self.send_header("Content-Type","application/json; charset=utf-8")
            self.send_header("Cache-Control","no-store");self.send_header("Content-Length",str(len(body)))
            self.end_headers();self.wfile.write(body)
        else:super().do_GET()

if __name__=="__main__":
    os.chdir(ROOT)
    porta=int(os.environ.get("PORT", "8000"))
    hospedado=bool(os.environ.get("PORT"))
    endereco="0.0.0.0" if hospedado else "127.0.0.1"
    print("Dashboard Hidrológico da 3ª DE", flush=True)
    print(f"Servidor em {endereco}:{porta}", flush=True)
    print("As consultas oficiais podem demorar na primeira atualização.", flush=True)
    try:
        server=ThreadingHTTPServer((endereco,porta),Handler)
    except OSError as e:
        print(f"ERRO ao iniciar na porta {porta}: {e}", flush=True)
        if not hospedado:
            input("Pressione Enter para fechar...")
        raise SystemExit(1)
    if not hospedado:
        threading.Timer(1.2,lambda:webbrowser.open(f"http://localhost:{porta}")).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
