/**
 * ESTRATÉGICO PRO — app.js v3.0 — COMPLETO Y LIMPIO
 * Módulos: Frecuencias · AF/Z-Score · EMA · Ciclos · Zonas ·
 *          Estados · Chi² · Entropía Shannon · Columnas ·
 *          Mitades · Paridad · Color · Vecinos · Patrones ·
 *          Capital (Martingala/Fibonacci/Paroli/D'Alembert) ·
 *          Señales · Recomendaciones · Resumen Ejecutivo
 */
'use strict';

/* ═══════════════════════════════════════
   CONSTANTES
   ═══════════════════════════════════════ */

const NUMEROS_ROJOS = new Set([1,3,5,7,9,12,14,16,18,19,21,23,25,27,30,32,34,36]);

const DOCENAS = {
  D1:{ min:1,  max:12,  nums:[1,2,3,4,5,6,7,8,9,10,11,12] },
  D2:{ min:13, max:24,  nums:[13,14,15,16,17,18,19,20,21,22,23,24] },
  D3:{ min:25, max:36,  nums:[25,26,27,28,29,30,31,32,33,34,35,36] },
};

const COLUMNAS = {
  C1:{ nums:[1,4,7,10,13,16,19,22,25,28,31,34], label:'Columna 1' },
  C2:{ nums:[2,5,8,11,14,17,20,23,26,29,32,35], label:'Columna 2' },
  C3:{ nums:[3,6,9,12,15,18,21,24,27,30,33,36], label:'Columna 3' },
};

const ZONAS = {
  VOISINS:  { nums:[22,18,29,7,28,12,35,3,26,0,32,15,19,4,21,2,25], label:'Voisins du Zéro' },
  TIERS:    { nums:[27,13,36,11,30,8,23,10,5,24,16,33],              label:'Tiers du Cylindre' },
  ORPHELINS:{ nums:[1,20,14,31,9,17,34,6],                           label:'Orphelins' },
  CERO:     { nums:[0],                                               label:'Cero' },
};

const CILINDRO = [0,32,15,19,4,21,2,25,17,34,6,27,13,36,11,30,8,23,10,5,24,16,33,1,20,14,31,9,22,18,29,7,28,12,35,3,26];

const DOCENA_COLORS = { D1:'#00D4FF', D2:'#10B981', D3:'#F59E0B' };
const ZONA_COLORS   = { VOISINS:'#00D4FF', TIERS:'#10B981', ORPHELINS:'#F59E0B', CERO:'#8B5CF6' };

const ESTADO_LABELS = {
  ideal:'IDEAL', sana:'SANA', advertencia:'ADVERTENCIA',
  peligro:'PELIGRO', explosion:'EXPLOSIÓN', reactivacion:'REACTIV.', sin_datos:'—',
};

/* ═══════════════════════════════════════
   ESTADO GLOBAL
   ═══════════════════════════════════════ */

const historial = [];

const G = {
  tiros: 0,
  docenas: {
    D1:{ f:{}, af:0, afDetalle:{}, aus:0, ciclo:null, cicloMin:null, cicloMax:null, cicloGaps:[],
         apariciones:0, pct:0, desv:0, ema:{e5:0,e10:0,e20:0}, tend:'', mom:0, estadoNombre:'sin_datos' },
    D2:{ f:{}, af:0, afDetalle:{}, aus:0, ciclo:null, cicloMin:null, cicloMax:null, cicloGaps:[],
         apariciones:0, pct:0, desv:0, ema:{e5:0,e10:0,e20:0}, tend:'', mom:0, estadoNombre:'sin_datos' },
    D3:{ f:{}, af:0, afDetalle:{}, aus:0, ciclo:null, cicloMin:null, cicloMax:null, cicloGaps:[],
         apariciones:0, pct:0, desv:0, ema:{e5:0,e10:0,e20:0}, tend:'', mom:0, estadoNombre:'sin_datos' },
  },
  columnas:  { C1:{}, C2:{}, C3:{} },
  zonas:     {},
  color:     { rojo:0, negro:0, verde:0 },
  paridad:   { par:0, impar:0 },
  mitades:   { baja:0, alta:0 },
  frecGlobal: new Array(37).fill(0),
  chi:       { valor:0, gl:36, pValor:'Sin datos' },
  entropia:  { shannon:0, max:Math.log2(37), norm:0 },
  senales:   [],
  alertsLog: [],
};

const Capital = {
  saldo:1000, apuestaBase:10, sistemaSel:'martingala',
  histCapital:[1000], rachaActual:0,
  fibonacci:[1,1], fibIdx:0,
};

/* ═══════════════════════════════════════
   UTILIDADES MATEMÁTICAS
   ═══════════════════════════════════════ */

function fDoc(d, n) {
  if (!historial.length) return 0;
  const { min, max } = DOCENAS[d];
  return historial.slice(-n).filter(x => x >= min && x <= max).length;
}

function fSet(nums, n) {
  const s = new Set(nums);
  return historial.slice(-n).filter(x => s.has(x)).length;
}

const espDoc = n => (12/37)*n;

function zScore(d, n) {
  const f = fDoc(d, n), esp = espDoc(n), p = 12/37;
  const sd = Math.sqrt(n * p * (1-p));
  return sd > 0 ? (f - esp) / sd : 0;
}

/**
 * MÓDULO DE ACELERACIÓN DE FRECUENCIA (AF) — COMPLETO
 *
 * Calcula AF en múltiples ventanas y deriva:
 *  - af5, af10, af20, af30  : Z-score de cada ventana (desviación vs esperado)
 *  - afDelta                : diferencia Z10 − Z20 (¿ganando/perdiendo impulso?)
 *  - afDelta2               : diferencia Z5 − Z10  (aceleración a corto plazo)
 *  - afTrend                : dirección sostenida ('acelerando'/'desacelerando'/'neutro')
 *  - afMagnitud             : valor resumen para señales (promedio ponderado)
 *  - afRachaPositiva        : cuántos tiros consecutivos lleva Z5 > 0
 *  - afRachaNegativa        : cuántos tiros consecutivos lleva Z5 < 0
 *  - af                     : valor principal (afDelta, compatible con código anterior)
 */
function calcAFDetalle(d) {
  const N = historial.length;
  if (N < 5) return {
    af5:0, af10:0, af20:0, af30:0,
    afDelta:0, afDelta2:0, afTrend:'neutro',
    afMagnitud:0, afRachaPositiva:0, afRachaNegativa:0, af:0,
  };

  const z5  = N >= 5  ? zScore(d, Math.min(5,  N)) : 0;
  const z10 = N >= 10 ? zScore(d, Math.min(10, N)) : 0;
  const z20 = N >= 20 ? zScore(d, Math.min(20, N)) : 0;
  const z30 = N >= 30 ? zScore(d, Math.min(30, N)) : 0;

  // Delta principal: Z10 − Z20 (aceleración reciente vs histórica media)
  const afDelta  = z10 - z20;
  // Delta corto:   Z5  − Z10 (impulso inmediato)
  const afDelta2 = z5  - z10;

  // Tendencia sostenida: los tres deltas apuntan en la misma dirección
  const afTrend =
    afDelta > 0.3  && afDelta2 > 0.15 ? 'acelerando'   :
    afDelta < -0.3 && afDelta2 < -0.15 ? 'desacelerando' : 'neutro';

  // Magnitud resumen (ponderada: más peso a ventana corta)
  const afMagnitud = z5 * 0.5 + z10 * 0.3 + z20 * 0.2;

  // Racha de Z5 positivo/negativo en últimos tiros
  const { min, max } = DOCENAS[d];
  let rachaPos = 0, rachaNeg = 0;
  // Calculamos Z5 deslizante sobre los últimos 15 tiros
  for (let i = N - 1; i >= Math.max(0, N - 15); i--) {
    const sliceEnd   = i + 1;
    const sliceStart = Math.max(0, sliceEnd - 5);
    const cnt5 = historial.slice(sliceStart, sliceEnd).filter(x => x >= min && x <= max).length;
    const len5 = sliceEnd - sliceStart;
    const z5i  = len5 >= 3 ? (cnt5 - espDoc(len5)) / Math.sqrt(len5*(12/37)*(25/37)) : 0;
    if (z5i > 0.1) { if (rachaNeg === 0) rachaPos++; else break; }
    else if (z5i < -0.1) { if (rachaPos === 0) rachaNeg++; else break; }
    else break;
  }

  return {
    af5: z5, af10: z10, af20: z20, af30: z30,
    afDelta, afDelta2, afTrend,
    afMagnitud,
    afRachaPositiva:  rachaPos,
    afRachaNegativa:  rachaNeg,
    af: afDelta,   // compatibilidad con código que usa data.af
  };
}

// Wrapper que devuelve solo el valor escalar (usado en calcEstado y señales simples)
function calcAF(d) {
  if (historial.length < 10) return 0;
  return zScore(d, Math.min(10, historial.length)) - zScore(d, Math.min(20, historial.length));
}

function ema(serie, periodo) {
  if (!serie.length) return 0;
  const k = 2 / (periodo+1);
  let v = serie[0];
  for (let i = 1; i < serie.length; i++) v = serie[i]*k + v*(1-k);
  return v;
}

function binaria(d) {
  const { min, max } = DOCENAS[d];
  return historial.map(n => (n >= min && n <= max) ? 1 : 0);
}

function calcAus(d) {
  const { min, max } = DOCENAS[d];
  let a = 0;
  for (let i = historial.length-1; i >= 0; i--) {
    if (historial[i] >= min && historial[i] <= max) break;
    a++;
  }
  return a;
}

function ausNum(n) {
  let a = 0;
  for (let i = historial.length-1; i >= 0; i--) {
    if (historial[i] === n) break;
    a++;
  }
  return a;
}

function calcCiclos(d) {
  const { min, max } = DOCENAS[d];
  const pos = historial.reduce((acc, n, i) => { if (n>=min && n<=max) acc.push(i); return acc; }, []);
  if (pos.length < 2) return { prom:null, min:null, max:null, gaps:[] };
  const gaps = pos.slice(1).map((p,i) => p - pos[i]);
  return { prom: gaps.reduce((a,b)=>a+b,0)/gaps.length, min:Math.min(...gaps), max:Math.max(...gaps), gaps };
}

function calcEstado(d) {
  if (historial.length < 5) return 'sin_datos';
  const aus = calcAus(d), f10 = fDoc(d, Math.min(10, historial.length)), af = calcAF(d);
  if (f10 >= 6)                                   return 'explosion';
  if (aus === 0 && f10 <= 2 && af < -0.3)         return 'reactivacion';
  if (aus >= 15)                                   return 'peligro';
  if (aus >= 8 || f10 <= 1)                        return 'advertencia';
  if (f10 >= 3 && f10 <= 5 && Math.abs(af) < 1.2) return 'ideal';
  return 'sana';
}

function colorNum(n) {
  if (n === 0) return 'verde';
  return NUMEROS_ROJOS.has(n) ? 'rojo' : 'negro';
}

function docenaDeNum(n) {
  if (n === 0) return 'CERO';
  if (n <= 12) return 'D1';
  if (n <= 24) return 'D2';
  return 'D3';
}

function columnaDeNum(n) {
  if (n === 0) return null;
  for (const [k,v] of Object.entries(COLUMNAS)) if (v.nums.includes(n)) return k;
  return null;
}

function calcRacha() {
  if (!historial.length) return { color:null, largo:0 };
  const base = colorNum(historial.at(-1));
  let largo = 1;
  for (let i = historial.length-2; i >= 0; i--) {
    if (colorNum(historial[i]) === base) largo++; else break;
  }
  return { color:base, largo };
}

function calcRachaDocena() {
  if (!historial.length) return { doc:null, largo:0 };
  const base = docenaDeNum(historial.at(-1));
  if (base === 'CERO') return { doc:'CERO', largo:1 };
  let largo = 1;
  for (let i = historial.length-2; i >= 0; i--) {
    if (docenaDeNum(historial[i]) === base) largo++; else break;
  }
  return { doc:base, largo };
}

function calcChiCuadrado() {
  const N = historial.length;
  if (N < 37) return { valor:0, gl:36, pValor:'Insuficientes datos (mín. 37)' };
  const esp = N/37;
  let chi = 0;
  for (let i = 0; i <= 36; i++) chi += Math.pow(G.frecGlobal[i] - esp, 2) / esp;
  const pValor =
    chi < 23  ? 'p > 0.99 (Excesiva regularidad)' :
    chi < 36  ? 'p ≈ 0.50 (Distribución normal)' :
    chi < 51  ? 'p ≈ 0.05 (Ligera desviación)' :
    chi < 63  ? 'p < 0.01 (Desviación significativa)' :
                'p < 0.001 (Muy sesgado)';
  return { valor:chi, gl:36, pValor };
}

function calcEntropia() {
  const N = historial.length;
  if (N < 5) return { shannon:0, max:Math.log2(37), norm:0 };
  let h = 0;
  for (let i = 0; i <= 36; i++) {
    const p = G.frecGlobal[i] / N;
    if (p > 0) h -= p * Math.log2(p);
  }
  const mx = Math.log2(37);
  return { shannon:h, max:mx, norm:(h/mx)*100 };
}

function hotCold(topN = 7) {
  const sorted = G.frecGlobal.map((cnt,num)=>({num,cnt})).sort((a,b)=>b.cnt-a.cnt);
  return { hot:sorted.slice(0,topN), cold:sorted.slice(-topN).reverse() };
}

function calcGaps() {
  return Array.from({length:37},(_,n)=>({ num:n, aus:ausNum(n) })).sort((a,b)=>b.aus-a.aus);
}

function calcProbabilidades() {
  const probs = {}, baseDoc = 12/37;
  for (const d of ['D1','D2','D3']) {
    const aus = G.docenas[d].aus, e5 = G.docenas[d].ema.e5;
    probs[d] = Math.max(0.05, Math.min(0.65, baseDoc + (aus/100)*0.12 - (e5 - baseDoc)*0.5));
  }
  const rc = calcRacha(), bc = 18/37;
  const adjC = rc.largo >= 4 ? Math.min(0.65, bc + rc.largo*0.015) : bc;
  probs.rojo = adjC; probs.negro = adjC; probs.verde = 1/37;
  for (const c of ['C1','C2','C3'])
    probs[c] = Math.max(0.1, Math.min(0.6, baseDoc + (baseDoc*10 - (G.columnas[c].f10||0))*0.02));
  return probs;
}

/* ─── Vecinos del cilindro ─── */
function vecinosDeNum(n, radio = 3) {
  const idx = CILINDRO.indexOf(n);
  if (idx === -1) return [];
  return Array.from({length:radio*2+1},(_,i) => {
    const j = ((idx + i - radio) % CILINDRO.length + CILINDRO.length) % CILINDRO.length;
    return CILINDRO[j];
  });
}

function calcCalorCilindro(n = 30) {
  const sl = historial.slice(-n);
  return CILINDRO.map(num => sl.filter(x => x === num).length);
}

/* ─── Patrones ─── */
function calcPatrones() {
  const N = historial.length;
  if (N < 6) return [];
  const pats = [];

  // Alternancia de colores
  let alt = 0;
  for (let i = N-1; i > 0 && i > N-11; i--) {
    if (colorNum(historial[i]) !== colorNum(historial[i-1])) alt++; else break;
  }
  if (alt >= 4) pats.push({ titulo:`Alternancia de colores ×${alt}`, desc:`Los últimos ${alt+1} tiros alternan color.`, icono:'🔄', fuerza: alt>=6?'alta':'media' });

  // Ciclo D1→D2→D3
  const ud = historial.slice(-6).map(n=>docenaDeNum(n)).filter(d=>d!=='CERO');
  if (ud.slice(-3).join('')==='D1D2D3') pats.push({ titulo:'Ciclo ascendente D1→D2→D3', desc:'Las últimas 3 docenas siguieron el orden natural.', icono:'↗', fuerza:'media' });
  if (ud.slice(-3).join('')==='D3D2D1') pats.push({ titulo:'Ciclo descendente D3→D2→D1', desc:'Las últimas 3 docenas siguieron el orden inverso.', icono:'↙', fuerza:'media' });

  // Número repetido
  const u5 = historial.slice(-5);
  const rep = [...new Set(u5.filter((n,i)=>u5.indexOf(n)!==i))];
  if (rep.length) pats.push({ titulo:`Número ${rep[0]} repetido en últimos 5`, desc:`El número ${rep[0]} apareció más de una vez recientemente.`, icono:'♊', fuerza:'baja' });

  // Zigzag de docenas
  let zz = 0;
  for (let i = N-1; i > 0 && i > N-8; i--) {
    const da=docenaDeNum(historial[i]), db=docenaDeNum(historial[i-1]);
    if (da!==db && da!=='CERO' && db!=='CERO') zz++; else break;
  }
  if (zz >= 5) pats.push({ titulo:`Zigzag de docenas ×${zz}`, desc:`Las docenas cambian en cada tiro hace ${zz} tiros.`, icono:'⚡', fuerza: zz>=7?'alta':'media' });

  // Alternancia par/impar
  const u8 = historial.slice(-8).filter(n=>n!==0);
  let pa = 0;
  for (let i = u8.length-1; i > 0; i--) {
    if ((u8[i]%2)!==(u8[i-1]%2)) pa++; else break;
  }
  if (pa >= 5) pats.push({ titulo:`Alternancia par/impar ×${pa}`, desc:`Par e impar se alternan hace ${pa} tiros.`, icono:'↕', fuerza:'media' });

  // Dominancia de mitad
  const u6 = historial.slice(-6).filter(n=>n!==0);
  if (u6.length >= 4 && u6.every(n=>n<=18)) pats.push({ titulo:'Dominancia mitad baja (1-18)', desc:`Los últimos ${u6.length} números cayeron en 1-18.`, icono:'⬇', fuerza:'media' });
  if (u6.length >= 4 && u6.every(n=>n>18))  pats.push({ titulo:'Dominancia mitad alta (19-36)', desc:`Los últimos ${u6.length} números cayeron en 19-36.`, icono:'⬆', fuerza:'media' });

  // Racha de columna
  const uc = historial.slice(-5).map(n=>columnaDeNum(n)).filter(Boolean);
  if (uc.length >= 4 && new Set(uc).size === 1) pats.push({ titulo:`${COLUMNAS[uc[0]].label} dominante ×${uc.length}`, desc:`Los últimos ${uc.length} números cayeron en la misma columna.`, icono:'📊', fuerza:'alta' });

  return pats;
}

/* ═══════════════════════════════════════
   MOTOR DE SEÑALES
   ═══════════════════════════════════════ */

function generarSenales() {
  const s = [];
  if (historial.length < 8) return s;

  for (const d of ['D1','D2','D3']) {
    const data = G.docenas[d];
    const f10=data.f.f10||0, aus=data.aus, af=data.af;
    const {e5,e10,e20} = data.ema;
    const est=data.estadoNombre, ciclo=data.ciclo;

    if (est==='explosion')
      s.push({ d, titulo:`${d} EXPLOSIÓN ACTIVA`, desc:`F10=${f10} muy por encima. Posible saturación.`, nivel:'explosion', icon:'🔥', conf:80 });

    if (aus >= 20)
      s.push({ d, titulo:`${d} AUSENCIA CRÍTICA (${aus})`, desc:`Sin aparecer ${aus} tiros. Ciclo≈${ciclo?ciclo.toFixed(1):'?'}.`, nivel:'alerta', icon:'🚨', conf:Math.min(93,72+aus) });
    else if (aus >= 10)
      s.push({ d, titulo:`${d} AUSENTE ${aus} TIROS`, desc:`Regresión inminente. Ciclo≈${ciclo?ciclo.toFixed(1):'?'}.`, nivel:'alta', icon:'⚡', conf:Math.min(85,60+aus*2) });

    if (est==='reactivacion')
      s.push({ d, titulo:`${d} REACTIVACIÓN`, desc:`Vuelve tras pausa. AF=${af.toFixed(2)}. EMA-5=${(e5*100).toFixed(1)}%.`, nivel:'media', icon:'♻️', conf:70 });

    if (e5>e10 && e10>e20 && f10>=3 && historial.length>=20)
      s.push({ d, titulo:`${d} CRUCE EMA ALCISTA`, desc:'EMA-5 > EMA-10 > EMA-20. Momentum confirmado.', nivel:'alta', icon:'📈', conf:76 });

    if (e5<e10 && e10<e20 && f10<=2 && historial.length>=20)
      s.push({ d, titulo:`${d} CRUCE EMA BAJISTA`, desc:'EMA-5 < EMA-10 < EMA-20. Evitar esta docena.', nivel:'baja', icon:'📉', conf:65 });

    // ── SEÑALES AF COMPLETAS ──
    const afd = data.afDetalle;
    if (afd.afTrend === 'acelerando' && afd.afMagnitud > 0.8)
      s.push({ d, titulo:`${d} ACELERACIÓN SOSTENIDA`, desc:`Z5=${afd.af5.toFixed(2)} Z10=${afd.af10.toFixed(2)} Z20=${afd.af20.toFixed(2)} — Δ=${afd.afDelta.toFixed(2)} Δ2=${afd.afDelta2.toFixed(2)}. Tendencia confirmada.`, nivel:'alta', icon:'🚀', conf:Math.min(88, 68 + Math.round(afd.afMagnitud * 10)) });

    else if (afd.af5 > 1.5 && afd.afDelta2 > 0)
      s.push({ d, titulo:`${d} IMPULSO CORTO FUERTE`, desc:`Z5=${afd.af5.toFixed(2)} — Frecuencia en los últimos 5 tiros muy por encima del esperado.`, nivel:'media', icon:'⚡', conf:72 });

    if (afd.afTrend === 'desacelerando' && afd.afMagnitud < -0.8)
      s.push({ d, titulo:`${d} DESACELERACIÓN SOSTENIDA`, desc:`Z5=${afd.af5.toFixed(2)} Z10=${afd.af10.toFixed(2)} Z20=${afd.af20.toFixed(2)} — Δ=${afd.afDelta.toFixed(2)}. Docena perdiendo impulso.`, nivel:'baja', icon:'📉', conf:65 });

    if (afd.afRachaPositiva >= 5)
      s.push({ d, titulo:`${d} RACHA AF POSITIVO ×${afd.afRachaPositiva}`, desc:`Lleva ${afd.afRachaPositiva} tiros con Z5 por encima de lo esperado.`, nivel:'media', icon:'🔺', conf:70 });

    if (afd.afRachaNegativa >= 5)
      s.push({ d, titulo:`${d} RACHA AF NEGATIVO ×${afd.afRachaNegativa}`, desc:`Lleva ${afd.afRachaNegativa} tiros con Z5 por debajo de lo esperado. Posible reversión.`, nivel:'media', icon:'🔻', conf:67 });

    // Cruce AF: Z5 cruza de negativo a positivo (señal de entrada)
    if (afd.af5 > 0.2 && afd.af10 < -0.2 && N >= 15)
      s.push({ d, titulo:`${d} CRUCE AF ALCISTA`, desc:`Z5=${afd.af5.toFixed(2)} cruza sobre Z10=${afd.af10.toFixed(2)}. Posible punto de entrada.`, nivel:'alta', icon:'✅', conf:74 });

    if (est==='ideal' && ciclo && Math.abs(aus-ciclo)<=1)
      s.push({ d, titulo:`${d} EN PUNTO DE CICLO`, desc:`Ausencia=${aus} ≈ Ciclo=${ciclo.toFixed(1)}. Timing favorable.`, nivel:'alta', icon:'🎯', conf:79 });
  }

  const racha = calcRacha();
  if (racha.largo >= 5) {
    const opp = racha.color === 'rojo' ? 'NEGRO' : 'ROJO';
    s.push({ d:'ALL', titulo:`RACHA ${racha.color?.toUpperCase()} ×${racha.largo}`, desc:`${racha.largo} consecutivos. Considerar ${opp}.`, nivel:racha.largo>=7?'alerta':'alta', icon:'🔴', conf:Math.min(85,50+racha.largo*6) });
  }

  const {par,impar} = G.paridad;
  if (par+impar >= 20) {
    const rp = par/(par+impar);
    if (rp < 0.35) s.push({ d:'ALL', titulo:'PARES FRÍOS', desc:`Solo ${(rp*100).toFixed(0)}% pares (esp: 48.6%).`, nivel:'media', icon:'⚖️', conf:67 });
    if (rp > 0.65) s.push({ d:'ALL', titulo:'IMPARES FRÍOS', desc:`Solo ${((1-rp)*100).toFixed(0)}% impares (esp: 48.6%).`, nivel:'media', icon:'⚖️', conf:67 });
  }

  for (const [zk,zv] of Object.entries(ZONAS)) {
    if (historial.length >= 30) {
      const fz = fSet(zv.nums,30), esp = (zv.nums.length/37)*30;
      if (fz < esp*0.45) s.push({ d:zk, titulo:`ZONA ${zk} FRÍA`, desc:`${fz} hits en 30 tiros (esp≈${esp.toFixed(0)}).`, nivel:'media', icon:'🧊', conf:66 });
    }
  }

  if (G.entropia.norm < 85 && historial.length >= 40)
    s.push({ d:'ALL', titulo:'ENTROPÍA BAJA — SESIÓN SESGADA', desc:`Entropía ${G.entropia.norm.toFixed(1)}% del máximo.`, nivel:'baja', icon:'📊', conf:60 });

  const ord = {alerta:5,explosion:4,alta:3,media:2,baja:1};
  s.sort((a,b)=>(ord[b.nivel]||0)-(ord[a.nivel]||0));
  return s.slice(0,12);
}

/* ═══════════════════════════════════════
   RECÁLCULO CENTRAL
   ═══════════════════════════════════════ */

function recalcularTodo() {
  const N = historial.length;
  G.tiros = N;

  G.frecGlobal.fill(0);
  for (const n of historial) G.frecGlobal[n]++;

  for (const d of ['D1','D2','D3']) {
    const data = G.docenas[d];
    data.f = { f10:fDoc(d,Math.min(10,N)), f20:fDoc(d,Math.min(20,N)), f30:fDoc(d,Math.min(30,N)), f50:fDoc(d,Math.min(50,N)) };
    data.afDetalle = calcAFDetalle(d);
    data.af  = data.afDetalle.af;
    data.aus = calcAus(d);
    const ci = calcCiclos(d);
    data.ciclo=ci.prom; data.cicloMin=ci.min; data.cicloMax=ci.max; data.cicloGaps=ci.gaps;
    data.apariciones = DOCENAS[d].nums.reduce((s,n)=>s+G.frecGlobal[n],0);
    data.pct  = N>0 ? (data.apariciones/N)*100 : 0;
    data.desv = data.pct - 32.43;
    const serie = binaria(d);
    const wS = Math.max(5, Math.min(20,N)), wM = Math.max(10,Math.min(30,N));
    data.ema = { e5:ema(serie.slice(-wS),5), e10:ema(serie.slice(-wM),10), e20:ema(serie,20) };
    const {e5,e10,e20} = data.ema;
    data.tend = e5>e10&&e10>e20?'subiendo':e5<e10&&e10<e20?'bajando':'lateral';
    if (serie.length >= 2) {
      const prevSerie = serie.slice(0,-1);
      const prevE5 = ema(prevSerie.slice(-Math.max(5,Math.min(20,N-1))),5);
      data.mom = e5 - prevE5;
    } else data.mom = 0;
    data.estadoNombre = calcEstado(d);
  }

  for (const [ck,cv] of Object.entries(COLUMNAS)) {
    let aus = 0;
    for (let i = N-1; i >= 0; i--) { if (cv.nums.includes(historial[i])) break; aus++; }
    G.columnas[ck] = {
      f10:fSet(cv.nums,Math.min(10,N)), f20:fSet(cv.nums,Math.min(20,N)),
      f30:fSet(cv.nums,Math.min(30,N)),
      total:historial.filter(n=>cv.nums.includes(n)).length, aus,
    };
  }

  for (const [zk,zv] of Object.entries(ZONAS)) {
    const s = new Set(zv.nums);
    G.zonas[zk] = {
      f10:fSet(zv.nums,Math.min(10,N)), f30:fSet(zv.nums,Math.min(30,N)),
      total:historial.filter(n=>s.has(n)).length,
    };
  }

  G.color={rojo:0,negro:0,verde:0}; G.paridad={par:0,impar:0}; G.mitades={baja:0,alta:0};
  for (const n of historial) {
    G.color[colorNum(n)]++;
    if (n!==0) { n%2===0?G.paridad.par++:G.paridad.impar++; n<=18?G.mitades.baja++:G.mitades.alta++; }
  }

  G.chi     = calcChiCuadrado();
  G.entropia = calcEntropia();
  G.senales  = generarSenales();
}

/* ═══════════════════════════════════════
   HELPERS DOM
   ═══════════════════════════════════════ */

const $id  = id => document.getElementById(id);
const setText = (id,v) => { const e=$id(id); if(e) e.textContent=v; };

function tendHTML(t) {
  return t==='subiendo'?'<span class="tend-up">▲ SUBIENDO</span>':
         t==='bajando' ?'<span class="tend-down">▼ BAJANDO</span>':
                        '<span class="tend-flat">→ LATERAL</span>';
}

function estadoColor(est) {
  return {ideal:'var(--green)',sana:'var(--blue)',advertencia:'var(--amber)',
          peligro:'var(--red)',explosion:'var(--purple)',reactivacion:'var(--cyan)'}[est] || 'var(--text-dim)';
}

/* ═══════════════════════════════════════
   RENDER — DOCENAS
   ═══════════════════════════════════════ */

function renderDocenas() {
  for (const d of ['D1','D2','D3']) {
    const pfx=d.toLowerCase(), data=G.docenas[d], est=data.estadoNombre, f=data.f, em=data.ema;
    setText(`${pfx}-f10`,  f.f10??'—'); setText(`${pfx}-f20`,f.f20??'—');
    setText(`${pfx}-f30`,  f.f30??'—'); setText(`${pfx}-f50`,f.f50??'—');
    setText(`${pfx}-af`,   data.af.toFixed(2));
    setText(`${pfx}-ema5`,  (em.e5 *100).toFixed(1)+'%');
    setText(`${pfx}-ema10`, (em.e10*100).toFixed(1)+'%');
    setText(`${pfx}-ema20`, (em.e20*100).toFixed(1)+'%');
    const te=$id(`${pfx}-tend`); if(te) te.innerHTML=tendHTML(data.tend);
    setText(`${pfx}-aus`,         data.aus);
    setText(`${pfx}-ciclo`,       data.ciclo    ?data.ciclo.toFixed(1)   :'—');
    setText(`${pfx}-ciclo-min`,   data.cicloMin ?data.cicloMin.toFixed(0):'—');
    setText(`${pfx}-ciclo-max`,   data.cicloMax ?data.cicloMax.toFixed(0):'—');
    setText(`${pfx}-apariciones`, data.apariciones);
    setText(`${pfx}-pct`,  data.pct.toFixed(1)+'%');
    setText(`${pfx}-desv`, (data.desv>=0?'+':'')+data.desv.toFixed(1)+'%');
    const badge=$id(`${pfx}-estado`);
    if(badge){ badge.textContent=ESTADO_LABELS[est]||est; badge.className=`badge ${est}`; }
    const card=$id(`card-${pfx}`);
    if(card) card.className=`docena-card estado-${est}`;
    const bar=$id(`${pfx}-bar`);
    if(bar){ bar.style.width=Math.min(100,(f.f10/10)*100)+'%'; bar.style.background=estadoColor(est); }
  }
}

/* ═══════════════════════════════════════
   RENDER — EMA TABLE
   ═══════════════════════════════════════ */

function renderEMA() {
  for (const [d,idx] of [['D1','1'],['D2','2'],['D3','3']]) {
    const data=G.docenas[d], em=data.ema;
    setText(`e${idx}-5`,  (em.e5 *100).toFixed(1)+'%');
    setText(`e${idx}-10`, (em.e10*100).toFixed(1)+'%');
    setText(`e${idx}-20`, (em.e20*100).toFixed(1)+'%');
    const te=$id(`e${idx}-tend`); if(te) te.innerHTML=tendHTML(data.tend);
    const mo=$id(`e${idx}-mom`);
    if(mo){
      const m=data.mom, s=m>0.01?'▲':m<-0.01?'▼':'—';
      mo.textContent=`${s} ${(m*100).toFixed(1)}%`;
      mo.className=m>0.01?'tend-up':m<-0.01?'tend-down':'tend-flat';
    }
  }
}

/* ═══════════════════════════════════════
   RENDER — AF BARRAS
   ═══════════════════════════════════════ */

function renderAF() {
  const cont = $id('af-visual'); if (!cont) return;

  if (G.tiros < 5) {
    cont.innerHTML = '<div style="font-family:var(--font-mono);font-size:10px;color:var(--text-dim);padding:8px 0">Registra al menos 5 tiros para calcular AF.</div>';
    return;
  }

  // Función auxiliar: color y clase según valor de Z
  const zCol  = z => z > 1.5 ? 'var(--green)' : z > 0.5 ? 'var(--cyan)' : z < -1.5 ? 'var(--red)' : z < -0.5 ? 'var(--amber)' : 'var(--blue)';
  const zCls  = z => z > 0.1 ? 'positive' : z < -0.1 ? 'negative' : 'neutral';
  const zBar  = z => {
    const pct = Math.min(100, (Math.abs(z) / 3) * 100);
    const col = zCol(z);
    // Barra centrada: positivo va a la derecha, negativo a la izquierda
    const side = z >= 0 ? 'left' : 'right';
    return `<div style="flex:1;height:10px;background:var(--bg-card-2);border:1px solid var(--border);border-radius:3px;overflow:hidden;position:relative">
      <div style="position:absolute;${side}:50%;width:${pct/2}%;height:100%;background:${col};border-radius:2px"></div>
      <div style="position:absolute;left:50%;top:0;bottom:0;width:1px;background:var(--border-light)"></div>
    </div>`;
  };
  const trendIcon = t => t === 'acelerando' ? '<span style="color:var(--green)">▲ ACELERANDO</span>' : t === 'desacelerando' ? '<span style="color:var(--red)">▼ DESACELER.</span>' : '<span style="color:var(--text-secondary)">→ NEUTRO</span>';

  cont.innerHTML = ['D1','D2','D3'].map(d => {
    const afd = G.docenas[d].afDetalle;
    if (!afd || afd.af5 === undefined) return '';

    const mainCol = zCol(afd.afMagnitud);
    const rachaStr = afd.afRachaPositiva >= 3 ? `<span style="color:var(--green)">▲×${afd.afRachaPositiva}</span>` :
                     afd.afRachaNegativa >= 3 ? `<span style="color:var(--red)">▼×${afd.afRachaNegativa}</span>` :
                     '<span style="color:var(--text-dim)">—</span>';

    return `<div style="background:var(--bg-card-2);border:1px solid var(--border);border-radius:6px;padding:8px 10px;margin-bottom:6px">
      <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:7px">
        <span style="font-family:var(--font-mono);font-size:13px;font-weight:700;color:${mainCol}">${d}</span>
        <span style="font-family:var(--font-mono);font-size:10px">${trendIcon(afd.afTrend)}</span>
        <span style="font-family:var(--font-mono);font-size:10px;color:var(--text-secondary)">RACHA: ${rachaStr}</span>
        <span style="font-family:var(--font-mono);font-size:11px;font-weight:700;color:${mainCol}">MAG ${afd.afMagnitud.toFixed(2)}</span>
      </div>

      <div style="display:grid;grid-template-columns:38px 1fr 44px;align-items:center;gap:5px;margin-bottom:3px">
        <span style="font-family:var(--font-mono);font-size:9px;color:var(--text-secondary)">Z5</span>
        ${zBar(afd.af5)}
        <span style="font-family:var(--font-mono);font-size:10px;font-weight:600" class="${zCls(afd.af5)}">${afd.af5.toFixed(2)}</span>
      </div>
      <div style="display:grid;grid-template-columns:38px 1fr 44px;align-items:center;gap:5px;margin-bottom:3px">
        <span style="font-family:var(--font-mono);font-size:9px;color:var(--text-secondary)">Z10</span>
        ${zBar(afd.af10)}
        <span style="font-family:var(--font-mono);font-size:10px;font-weight:600" class="${zCls(afd.af10)}">${afd.af10.toFixed(2)}</span>
      </div>
      <div style="display:grid;grid-template-columns:38px 1fr 44px;align-items:center;gap:5px;margin-bottom:3px">
        <span style="font-family:var(--font-mono);font-size:9px;color:var(--text-secondary)">Z20</span>
        ${zBar(afd.af20)}
        <span style="font-family:var(--font-mono);font-size:10px;font-weight:600" class="${zCls(afd.af20)}">${afd.af20.toFixed(2)}</span>
      </div>
      <div style="display:grid;grid-template-columns:38px 1fr 44px;align-items:center;gap:5px">
        <span style="font-family:var(--font-mono);font-size:9px;color:var(--text-secondary)">Z30</span>
        ${zBar(afd.af30)}
        <span style="font-family:var(--font-mono);font-size:10px;font-weight:600" class="${zCls(afd.af30)}">${afd.af30.toFixed(2)}</span>
      </div>

      <div style="display:flex;gap:14px;margin-top:7px;padding-top:6px;border-top:1px solid var(--border)">
        <span style="font-family:var(--font-mono);font-size:9px">
          <span style="color:var(--text-secondary)">Δ(Z10−Z20) </span>
          <span style="font-weight:700;color:${afd.afDelta>0?'var(--green)':'var(--red)'}">${afd.afDelta>=0?'+':''}${afd.afDelta.toFixed(2)}</span>
        </span>
        <span style="font-family:var(--font-mono);font-size:9px">
          <span style="color:var(--text-secondary)">Δ2(Z5−Z10) </span>
          <span style="font-weight:700;color:${afd.afDelta2>0?'var(--green)':'var(--red)'}">${afd.afDelta2>=0?'+':''}${afd.afDelta2.toFixed(2)}</span>
        </span>
      </div>
    </div>`;
  }).join('');
}

/* ═══════════════════════════════════════
   RENDER — GRÁFICA CICLOS (Canvas)
   ═══════════════════════════════════════ */

function renderCicloCanvas() {
  const canvas=$id('ciclo-canvas'); if(!canvas) return;
  const ctx=canvas.getContext('2d');
  const W=canvas.offsetWidth||320, H=120;
  canvas.width=W; canvas.height=H;
  ctx.clearRect(0,0,W,H);
  ctx.fillStyle='#0D1117'; ctx.fillRect(0,0,W,H);
  const N=historial.length;
  if(N<4){
    ctx.fillStyle='#334155'; ctx.font='10px JetBrains Mono,monospace'; ctx.textAlign='center';
    ctx.fillText('Registra más tiros para ver la gráfica',W/2,H/2); return;
  }
  const PAD={l:28,r:8,t:8,b:18}, IW=W-PAD.l-PAD.r, IH=H-PAD.t-PAD.b;
  ctx.strokeStyle='#1E293B'; ctx.lineWidth=1;
  for(let y=0;y<=4;y++){
    const yy=PAD.t+IH-(y/4)*IH;
    ctx.beginPath(); ctx.moveTo(PAD.l,yy); ctx.lineTo(PAD.l+IW,yy); ctx.stroke();
    ctx.fillStyle='#334155'; ctx.font='8px JetBrains Mono,monospace'; ctx.textAlign='right';
    ctx.fillText((y*25)+'%',PAD.l-3,yy+3);
  }
  const docColors={D1:'#00D4FF',D2:'#10B981',D3:'#F59E0B'};
  for(const [d,color] of Object.entries(docColors)){
    const {min,max}=DOCENAS[d];
    ctx.strokeStyle=color; ctx.lineWidth=1.5; ctx.beginPath();
    let count=0;
    for(let i=0;i<N;i++){
      if(historial[i]>=min&&historial[i]<=max) count++;
      const x=PAD.l+(i/(N-1))*IW;
      const y=PAD.t+IH-((count/(i+1))*100/33.33)*IH;
      i===0?ctx.moveTo(x,Math.max(PAD.t,Math.min(PAD.t+IH,y))):ctx.lineTo(x,Math.max(PAD.t,Math.min(PAD.t+IH,y)));
    }
    ctx.stroke();
  }
  const yRef=PAD.t+IH-((32.43/33.33)*IH);
  ctx.setLineDash([4,4]); ctx.strokeStyle='#334155'; ctx.lineWidth=1;
  ctx.beginPath(); ctx.moveTo(PAD.l,yRef); ctx.lineTo(PAD.l+IW,yRef); ctx.stroke();
  ctx.setLineDash([]);
  const leg=$id('ciclo-legend');
  if(leg) leg.innerHTML=Object.entries(docColors).map(([d,c])=>
    `<span class="ciclo-leg-item"><span class="ciclo-dot" style="background:${c}"></span>${d} — ${G.docenas[d].pct.toFixed(1)}%</span>`
  ).join('');
}

/* ═══════════════════════════════════════
   RENDER — ZONAS
   ═══════════════════════════════════════ */

function renderZonas() {
  const cont=$id('zonas-grid'); if(!cont) return;
  cont.innerHTML=Object.entries(ZONAS).map(([k,z])=>{
    const data=G.zonas[k]||{f10:0,f30:0,total:0};
    const pct=G.tiros>0?((data.total/G.tiros)*100).toFixed(1):'0.0';
    const esp=((z.nums.length/37)*100).toFixed(1), color=ZONA_COLORS[k]||'var(--cyan)';
    return `<div class="zona-card" style="border-left:3px solid ${color}">
      <div class="zona-name" style="color:${color}">${z.label}</div>
      <div class="zona-nums">${z.nums.slice(0,8).join('·')}${z.nums.length>8?'…':''}</div>
      <div class="zona-stats">F10:<strong>${data.f10}</strong> F30:<strong>${data.f30}</strong> T:<strong>${data.total}</strong><br>
        Real:<strong>${pct}%</strong> Esp:${esp}%</div>
    </div>`;
  }).join('');
}

/* ═══════════════════════════════════════
   RENDER — FRECUENCIAS
   ═══════════════════════════════════════ */

function renderFreqChart() {
  const cont=$id('freq-chart'); if(!cont) return;
  const mx=Math.max(...G.frecGlobal,1);
  cont.innerHTML=G.frecGlobal.map((cnt,n)=>{
    const pct=(cnt/mx)*100, color=n===0?'var(--purple)':NUMEROS_ROJOS.has(n)?'var(--red)':'#64748B';
    return `<div class="freq-row">
      <span class="freq-num" style="color:${color}">${n}</span>
      <div class="freq-bar-wrap"><div class="freq-bar" style="width:${pct}%;background:${color}"></div></div>
      <span class="freq-cnt">${cnt}</span>
    </div>`;
  }).join('');
  setText('freq-total',`${G.tiros} tiros`);
}

/* ═══════════════════════════════════════
   RENDER — SEÑALES
   ═══════════════════════════════════════ */

function renderSenales() {
  const cont=$id('signals-list'), count=$id('signals-count'); if(!cont) return;
  if(!G.senales.length){
    cont.innerHTML='<div class="empty-msg">Sin datos — registra al menos 10 tiros</div>';
    if(count) count.textContent='0'; return;
  }
  if(count) count.textContent=G.senales.length;
  cont.innerHTML=G.senales.map(s=>`
    <div class="signal-card ${s.nivel}">
      <span class="sig-icon">${s.icon}</span>
      <div class="sig-body"><div class="sig-title">${s.titulo}</div><div class="sig-desc">${s.desc}</div></div>
      <span class="sig-conf ${s.nivel}">${s.conf?s.conf+'%':''}</span>
    </div>`).join('');
  const top=G.senales[0], banner=$id('signal-banner');
  if(banner&&top&&(top.nivel==='alerta'||top.nivel==='explosion')){
    banner.style.display='flex';
    setText('sb-icon',top.icon); setText('sb-text',top.titulo+' — '+top.desc); setText('sb-conf',top.conf?top.conf+'%':'');
  } else if(banner) banner.style.display='none';
}

/* ═══════════════════════════════════════
   RENDER — PROBABILIDADES
   ═══════════════════════════════════════ */

function renderProbabilidades() {
  const cont=$id('prob-panel'); if(!cont) return;
  if(G.tiros<5){ cont.innerHTML='<div class="empty-msg">Más tiros necesarios.</div>'; return; }
  const probs=calcProbabilidades();
  const items=[
    {label:'Docena 1 (1–12)',key:'D1',color:'var(--cyan)'},
    {label:'Docena 2 (13–24)',key:'D2',color:'var(--green)'},
    {label:'Docena 3 (25–36)',key:'D3',color:'var(--amber)'},
    {label:'Color Rojo',key:'rojo',color:'var(--red)'},
    {label:'Color Negro',key:'negro',color:'#64748B'},
    {label:'Columna 1',key:'C1',color:'var(--blue)'},
    {label:'Columna 2',key:'C2',color:'var(--purple)'},
    {label:'Columna 3',key:'C3',color:'var(--orange)'},
  ];
  cont.innerHTML=items.map(it=>{
    const p=probs[it.key]||0;
    return `<div class="prob-row">
      <span class="prob-label">${it.label}</span>
      <div class="prob-bar-track"><div class="prob-bar-fill" style="width:${Math.min(100,p*100)}%;background:${it.color}"></div></div>
      <span class="prob-pct">${(p*100).toFixed(1)}%</span>
    </div>`;
  }).join('');
}

/* ═══════════════════════════════════════
   RENDER — ALERTAS LOG
   ═══════════════════════════════════════ */

function agregarAlerta(msg, tipo='info') {
  const time=new Date().toLocaleTimeString('es-CO',{hour:'2-digit',minute:'2-digit',second:'2-digit'});
  G.alertsLog.unshift({msg,tipo,time});
  if(G.alertsLog.length>50) G.alertsLog.pop();
}

function renderAlertsLog() {
  const cont=$id('alerts-log'); if(!cont) return;
  if(!G.alertsLog.length){ cont.innerHTML='<div class="empty-msg">Sin alertas aún.</div>'; return; }
  cont.innerHTML=G.alertsLog.slice(0,20).map(a=>
    `<div class="alert-entry ${a.tipo}"><span class="alert-time">${a.time}</span><span class="alert-msg">${a.msg}</span></div>`
  ).join('');
}

/* ═══════════════════════════════════════
   RENDER — ESTADÍSTICAS
   ═══════════════════════════════════════ */

function renderEstadisticas() {
  // Stats globales
  const cont=$id('stats-global'); if(!cont) return;
  const N=G.tiros, racha=calcRacha();
  const maxNum=G.frecGlobal.indexOf(Math.max(...G.frecGlobal));
  const minNum=G.frecGlobal.indexOf(Math.min(...G.frecGlobal));
  const items=[
    {label:'TOTAL TIROS',val:N,sub:''},
    {label:'NÚMERO MÁS VISTO',val:maxNum,sub:G.frecGlobal[maxNum]+' veces'},
    {label:'NÚMERO MENOS VISTO',val:minNum,sub:G.frecGlobal[minNum]+' veces'},
    {label:'RACHA COLOR ACTUAL',val:racha.color?`${racha.color.toUpperCase()} ×${racha.largo}`:'—',sub:''},
    {label:'PARES TOTAL',val:G.paridad.par,sub:N>0?((G.paridad.par/N)*100).toFixed(1)+'%':'—'},
    {label:'IMPARES TOTAL',val:G.paridad.impar,sub:N>0?((G.paridad.impar/N)*100).toFixed(1)+'%':'—'},
    {label:'MITAD BAJA (1-18)',val:G.mitades.baja,sub:N>0?((G.mitades.baja/N)*100).toFixed(1)+'%':'—'},
    {label:'MITAD ALTA (19-36)',val:G.mitades.alta,sub:N>0?((G.mitades.alta/N)*100).toFixed(1)+'%':'—'},
    {label:'CEROS TOTALES',val:G.frecGlobal[0],sub:N>0?((G.frecGlobal[0]/N)*100).toFixed(1)+'%':'—'},
    {label:'ROJOS TOTALES',val:G.color.rojo,sub:N>0?((G.color.rojo/N)*100).toFixed(1)+'%':'—'},
    {label:'NEGROS TOTALES',val:G.color.negro,sub:N>0?((G.color.negro/N)*100).toFixed(1)+'%':'—'},
    {label:'CHI-CUADRADO',val:G.chi.valor.toFixed(2),sub:G.chi.pValor},
  ];
  cont.innerHTML=items.map(it=>`<div class="stat-block">
    <div class="stat-block-label">${it.label}</div>
    <div class="stat-block-value">${it.val}</div>
    ${it.sub?`<div class="stat-block-sub">${it.sub}`:''}
  </div>`).join('');

  // Chi
  const chiC=$id('chi-panel'); if(chiC){
    const {valor,gl,pValor}=G.chi;
    const col=valor>63?'var(--red)':valor>51?'var(--amber)':valor<23?'var(--blue)':'var(--green)';
    const interp=valor>63?'Desviación muy significativa. Posible sesgo.':valor>51?'Ligera desviación. Observar más tiros.':valor<23?'Distribución excesivamente regular.':'Normal para ruleta aleatoria.';
    chiC.innerHTML=`
      <div class="chi-row"><span>Valor χ²</span><span style="color:${col}">${valor.toFixed(3)}</span></div>
      <div class="chi-row"><span>Grados de libertad</span><span>${gl}</span></div>
      <div class="chi-row"><span>P-Valor</span><span style="color:${col}">${pValor}</span></div>
      <div class="chi-row"><span>Interpretación</span><span style="color:${col}">${interp}</span></div>
      <div class="chi-row"><span>Muestras</span><span>${N}</span></div>
      ${N<37?'<div style="color:var(--amber);font-family:var(--font-mono);font-size:10px;margin-top:5px">⚠ Mínimo 37 tiros para chi² válido</div>':''}`;
  }

  // Entropía
  const entC=$id('entropia-panel'); if(entC){
    const {shannon,max,norm}=G.entropia;
    const col=norm>90?'var(--green)':norm>75?'var(--amber)':'var(--red)';
    entC.innerHTML=`
      <div class="entropia-label">Shannon: ${shannon.toFixed(4)} bits / máx ${max.toFixed(4)} bits</div>
      <div class="entropia-track">
        <div class="entropia-fill" style="width:${norm.toFixed(1)}%;background:${col}"></div>
        <span class="entropia-val" style="color:${col}">${norm.toFixed(1)}%</span>
      </div>
      <div class="chi-row" style="margin-top:8px"><span>Diversidad números</span><span style="color:${col}">${norm.toFixed(1)}% del máximo</span></div>
      <div class="chi-row"><span>Números sin aparecer</span><span>${G.frecGlobal.filter(c=>c===0).length} de 37</span></div>
      <div class="chi-row"><span>Interpretación</span><span style="color:${col}">${norm>90?'Alta aleatoriedad.':norm>75?'Moderada. Algunos dominan.':'Baja. Sesión sesgada.'}</span></div>`;
  }

  // Hot/Cold
  const hcC=$id('hot-cold'); if(hcC){
    const {hot,cold}=hotCold(7), mx2=Math.max(...G.frecGlobal,1);
    const rowH=(item,color)=>{
      const pct=(item.cnt/mx2)*100, nc=colorNum(item.num);
      const nc2=nc==='rojo'?'#fca5a5':nc==='verde'?'#86efac':'#94a3b8';
      return `<div class="hc-item"><span class="hc-num" style="color:${nc2}">${item.num}</span>
        <div class="hc-bar-wrap"><div class="hc-bar" style="width:${pct}%;background:${color}"></div></div>
        <span class="hc-cnt">${item.cnt}</span></div>`;
    };
    hcC.innerHTML=`<div class="hot-section"><div class="hc-title hot">🔥 MÁS FRECUENTES</div><div class="hc-list">${hot.map(i=>rowH(i,'var(--red)')).join('')}</div></div>
      <div class="cold-section"><div class="hc-title cold">🧊 MENOS FRECUENTES</div><div class="hc-list">${cold.map(i=>rowH(i,'var(--blue)')).join('')}</div></div>`;
  }

  // Color dist
  const cdC=$id('color-dist'); if(cdC){
    const N2=G.tiros;
    const items2=[{label:'🔴 Rojo',cnt:G.color.rojo,color:'var(--red)',esp:18/37},{label:'⚫ Negro',cnt:G.color.negro,color:'#64748B',esp:18/37},{label:'🟢 Verde',cnt:G.color.verde,color:'var(--green)',esp:1/37}];
    cdC.innerHTML=items2.map(it=>{
      const pct=N2>0?(it.cnt/N2)*100:0, esp=it.esp*100, diff=pct-esp;
      const dc=Math.abs(diff)<5?'var(--green)':Math.abs(diff)<10?'var(--amber)':'var(--red)';
      return `<div class="cdist-row"><span class="cdist-label">${it.label}</span>
        <div class="cdist-track"><div class="cdist-fill" style="width:${pct}%;background:${it.color}"></div></div>
        <span class="cdist-val"><strong>${it.cnt}</strong> (${pct.toFixed(1)}% <span style="color:${dc}">${diff>=0?'+':''}${diff.toFixed(1)}%</span>)</span></div>`;
    }).join('');
  }

  // Gaps
  const gC=$id('gaps-panel'); if(gC){
    const gaps=calcGaps(), top5=gaps.slice(0,5);
    const avg=G.tiros>0?(gaps.reduce((a,b)=>a+b.aus,0)/37).toFixed(1):'—';
    gC.innerHTML=`
      <div class="gap-row"><span>Número más ausente</span><span>${gaps[0]?.num} (${gaps[0]?.aus} tiros)</span></div>
      <div class="gap-row"><span>2° más ausente</span><span>${gaps[1]?.num} (${gaps[1]?.aus} tiros)</span></div>
      <div class="gap-row"><span>3° más ausente</span><span>${gaps[2]?.num} (${gaps[2]?.aus} tiros)</span></div>
      <div class="gap-row"><span>Ausencia promedio</span><span>${avg} tiros</span></div>
      <div class="gap-row"><span>Sin aparecer</span><span>${G.frecGlobal.filter(c=>c===0).length} de 37</span></div>
      <div style="margin-top:7px;font-family:var(--font-mono);font-size:10px;color:var(--text-secondary)">TOP 5: ${top5.map(g=>`<span style="color:var(--amber)">${g.num}(${g.aus})</span>`).join(' · ')}</div>`;
  }
}

/* ═══════════════════════════════════════
   RENDER — APUESTAS SIMPLES
   ═══════════════════════════════════════ */

function apuestaBlock(items) {
  return items.map(it=>{
    const pct=it.total>0?(it.cnt/it.total)*100:0, esp=it.esp*100;
    const calor=pct>esp+8?'caliente':pct<esp-8?'fria':'normal';
    const calLabel=calor==='caliente'?'CALIENTE 🔥':calor==='fria'?'FRÍA 🧊':'NORMAL ✓';
    return `<div class="apuesta-row">
      <span class="ap-label">${it.label}</span>
      <div class="ap-bar-track"><div class="ap-bar-fill" style="width:${Math.min(100,pct)}%;background:${it.color}"></div></div>
      <span class="ap-val" style="color:${it.color}">${pct.toFixed(1)}%</span>
      <span class="ap-cnt">F10:${it.f10}</span>
      <span class="ap-señal ${calor}">${calLabel}</span>
    </div>`;
  }).join('');
}

function renderParidad() {
  const cont=$id('paridad-panel'); if(!cont) return;
  const N=G.paridad.par+G.paridad.impar;
  const f10p=historial.slice(-10).filter(n=>n!==0&&n%2===0).length;
  const f10i=historial.slice(-10).filter(n=>n!==0&&n%2!==0).length;
  let ausP=0; for(let i=G.tiros-1;i>=0;i--){if(historial[i]!==0&&historial[i]%2===0)break;ausP++;}
  cont.innerHTML=`<div class="apuesta-block">${apuestaBlock([
    {label:'PAR',cnt:G.paridad.par,total:N,esp:0.5,color:'var(--blue)',f10:f10p},
    {label:'IMPAR',cnt:G.paridad.impar,total:N,esp:0.5,color:'var(--purple)',f10:f10i},
  ])}</div><div style="font-family:var(--font-mono);font-size:10px;color:var(--text-secondary);margin-top:7px">Esp: 48.65% excl. cero | Ult. aus. PAR: ${ausP} tiros</div>`;
}

function renderMitades() {
  const cont=$id('mitades-panel'); if(!cont) return;
  const N=G.mitades.baja+G.mitades.alta;
  const f10b=historial.slice(-10).filter(n=>n>=1&&n<=18).length;
  const f10a=historial.slice(-10).filter(n=>n>=19&&n<=36).length;
  cont.innerHTML=`<div class="apuesta-block">${apuestaBlock([
    {label:'BAJA (1–18)',cnt:G.mitades.baja,total:N,esp:0.5,color:'var(--green)',f10:f10b},
    {label:'ALTA (19–36)',cnt:G.mitades.alta,total:N,esp:0.5,color:'var(--amber)',f10:f10a},
  ])}</div><div style="font-family:var(--font-mono);font-size:10px;color:var(--text-secondary);margin-top:7px">Esp: 48.65% por mitad (excl. cero)</div>`;
}

function renderColumnas() {
  const cont=$id('columnas-panel'); if(!cont) return;
  cont.innerHTML=`<div class="apuesta-block">${apuestaBlock(
    ['C1','C2','C3'].map((c,i)=>{
      const dc=G.columnas[c];
      return {label:`${COLUMNAS[c].label} (aus:${dc.aus})`,cnt:dc.total||0,total:G.tiros,esp:12/37,color:['var(--cyan)','var(--purple)','var(--orange)'][i],f10:dc.f10||0};
    })
  )}</div><div style="font-family:var(--font-mono);font-size:10px;color:var(--text-secondary);margin-top:7px">Esp: 32.43% por columna</div>`;
}

function renderColorApuesta() {
  const cont=$id('color-panel'); if(!cont) return;
  const f10r=historial.slice(-10).filter(n=>NUMEROS_ROJOS.has(n)).length;
  const f10n=historial.slice(-10).filter(n=>n!==0&&!NUMEROS_ROJOS.has(n)).length;
  const f10v=historial.slice(-10).filter(n=>n===0).length;
  cont.innerHTML=`<div class="apuesta-block">${apuestaBlock([
    {label:'ROJO',cnt:G.color.rojo,total:G.tiros,esp:18/37,color:'var(--red)',f10:f10r},
    {label:'NEGRO',cnt:G.color.negro,total:G.tiros,esp:18/37,color:'#64748B',f10:f10n},
    {label:'VERDE (0)',cnt:G.color.verde,total:G.tiros,esp:1/37,color:'var(--green)',f10:f10v},
  ])}</div>`;
}

function renderRecomendacion() {
  const cont=$id('recomendacion-panel');
  if(!cont||G.tiros<10){ if(cont) cont.innerHTML='<div class="empty-msg">Registra al menos 10 tiros.</div>'; return; }
  const recs=[];
  const colorNivel={alerta:'var(--red)',alta:'var(--green)',media:'var(--amber)',baja:'var(--blue)'};

  // Docena más ausente
  const docAus=['D1','D2','D3'].map(d=>({d,aus:G.docenas[d].aus,ciclo:G.docenas[d].ciclo})).sort((a,b)=>b.aus-a.aus);
  if(docAus[0].aus>=8) recs.push({titulo:`⚡ Considerar ${docAus[0].d}`,body:`Ausente <strong>${docAus[0].aus}</strong> tiros. Ciclo≈${docAus[0].ciclo?docAus[0].ciclo.toFixed(1):'~3'}. Presión acumulada.`,nivel:'alta'});

  // Racha de color (bug corregido)
  const racha=calcRacha();
  if(racha.largo>=5){
    const opp=racha.color==='rojo'?'NEGRO':'ROJO';
    recs.push({titulo:`🔴 Racha ${racha.color?.toUpperCase()} ×${racha.largo}`,body:`${racha.largo} del mismo color. Considerar <strong>${opp}</strong>.`,nivel:racha.largo>=7?'alerta':'media'});
  }

  // Racha de docena
  const rDoc=calcRachaDocena();
  if(rDoc.largo>=4&&rDoc.doc!=='CERO') recs.push({titulo:`📊 Racha ${rDoc.doc} ×${rDoc.largo}`,body:`<strong>${rDoc.doc}</strong> lleva ${rDoc.largo} tiros consecutivos. Alta saturación.`,nivel:'media'});

  // Columna fría
  const cAus=['C1','C2','C3'].map(c=>({c,aus:G.columnas[c].aus||0})).sort((a,b)=>b.aus-a.aus);
  if(cAus[0].aus>=10) recs.push({titulo:`🧊 ${COLUMNAS[cAus[0].c].label} fría`,body:`Sin aparecer <strong>${cAus[0].aus}</strong> tiros. Por encima del ciclo esperado.`,nivel:'media'});

  // Paridad
  const tot=G.paridad.par+G.paridad.impar;
  if(tot>=20){
    const rp=G.paridad.par/tot;
    if(rp<0.38) recs.push({titulo:'⚖️ Pares subrepresentados',body:`Solo <strong>${(rp*100).toFixed(0)}%</strong> pares (esp: 48.6%). Considerar pares.`,nivel:'baja'});
    else if(rp>0.62) recs.push({titulo:'⚖️ Impares subrepresentados',body:`Solo <strong>${((1-rp)*100).toFixed(0)}%</strong> impares. Considerar impares.`,nivel:'baja'});
  }

  // EMA alcista
  for(const d of ['D1','D2','D3']){
    const {e5,e10,e20}=G.docenas[d].ema;
    if(e5>e10&&e10>e20&&G.docenas[d].f.f10>=4){
      recs.push({titulo:`📈 ${d} con momentum alcista`,body:`EMA-5>EMA-10>EMA-20. Tendencia positiva. F10=${G.docenas[d].f.f10}.`,nivel:'alta'});
      break;
    }
  }

  if(!recs.length) recs.push({titulo:'✓ Sin sesgo identificado',body:'Los indicadores no muestran ventajas claras. Esperar más tiros.',nivel:'baja'});

  cont.innerHTML=recs.map(r=>`<div class="rec-card" style="border-left-color:${colorNivel[r.nivel]||'var(--cyan)'}">
    <div class="rec-title" style="color:${colorNivel[r.nivel]||'var(--cyan)'}">${r.titulo}</div>
    <div class="rec-body">${r.body}</div>
  </div>`).join('');
}

function renderApuestas() {
  renderParidad(); renderMitades(); renderColumnas(); renderColorApuesta(); renderRecomendacion();
}

/* ═══════════════════════════════════════
   RENDER — VECINOS & MAPA CALOR
   ═══════════════════════════════════════ */

function renderVecinos() {
  const cont=$id('vecinos-panel'); if(!cont) return;
  if(G.tiros<5){ cont.innerHTML='<div class="empty-msg">Registra más tiros.</div>'; return; }
  const ultimo=historial.at(-1);
  const calor=calcCalorCilindro(30), maxCal=Math.max(...calor,1);

  // Sector más caliente (ventana 5)
  let maxSect=0, maxIdx=0;
  for(let i=0;i<CILINDRO.length;i++){
    const sect=[0,1,2,3,4].reduce((s,d)=>s+calor[(i+d)%CILINDRO.length],0);
    if(sect>maxSect){maxSect=sect;maxIdx=i;}
  }
  const sectCal=Array.from({length:5},(_,i)=>CILINDRO[(maxIdx+i)%CILINDRO.length]);
  const vecinosU=ultimo!==undefined?vecinosDeNum(ultimo,3):[];

  cont.innerHTML=`
    <div class="vecinos-section">
      <div class="vecinos-title">VECINOS DEL ÚLTIMO (${ultimo??'—'}) ±3</div>
      <div class="vecinos-chips">
        ${vecinosU.map(n=>{
          const color=colorNum(n), cls=n===0?'hchip-0':`hchip-${color}`;
          const center=n===ultimo?'style="outline:2px solid var(--cyan);outline-offset:2px"':'';
          return `<span class="hchip ${cls}" ${center}>${n}</span>`;
        }).join('')}
      </div>
    </div>
    <div class="vecinos-section" style="margin-top:11px">
      <div class="vecinos-title">SECTOR MÁS CALIENTE (últimos 30)</div>
      <div class="vecinos-chips">
        ${sectCal.map(n=>{const c=colorNum(n),cls=n===0?'hchip-0':`hchip-${c}`;return `<span class="hchip ${cls}">${n}</span>`;}).join('')}
        <span style="font-family:var(--font-mono);font-size:10px;color:var(--amber);margin-left:6px">${maxSect} hits</span>
      </div>
    </div>
    <div class="vecinos-section" style="margin-top:11px">
      <div class="vecinos-title">MAPA DE CALOR — CILINDRO (últimos 30)</div>
      <div class="cilindro-heatmap">
        ${CILINDRO.map((n,i)=>{
          const c=calor[i];
          const bg=c===0?'var(--bg-card-2)':c>=maxCal*0.7?'rgba(239,68,68,0.4)':c>=maxCal*0.4?'rgba(245,158,11,0.3)':'rgba(59,130,246,0.2)';
          const tc=n===0?'#86efac':NUMEROS_ROJOS.has(n)?'#fca5a5':'#94a3b8';
          return `<span class="cilindro-num" style="background:${bg};color:${tc}" title="${n}: ${c} hits">${n}<sup>${c}</sup></span>`;
        }).join('')}
      </div>
    </div>`;
}

/* ═══════════════════════════════════════
   RENDER — PATRONES
   ═══════════════════════════════════════ */

function renderPatrones() {
  const cont=$id('patrones-panel'); if(!cont) return;
  const pats=calcPatrones();
  if(!pats.length){ cont.innerHTML='<div class="empty-msg">Sin patrones detectados aún — registra más tiros.</div>'; return; }
  const cf={alta:'var(--green)',media:'var(--amber)',baja:'var(--blue)'};
  cont.innerHTML=pats.map(p=>`<div class="pattern-card" style="border-left-color:${cf[p.fuerza]||'var(--cyan)'}">
    <div class="pattern-header">
      <span class="pattern-icon">${p.icono}</span>
      <span class="pattern-title">${p.titulo}</span>
      <span class="pattern-badge" style="color:${cf[p.fuerza]}">${p.fuerza.toUpperCase()}</span>
    </div>
    <div class="pattern-desc">${p.desc}</div>
  </div>`).join('');
}

/* ═══════════════════════════════════════
   RENDER — GESTIÓN DE CAPITAL
   ═══════════════════════════════════════ */

function calcApuestaSiguiente() {
  const {sistemaSel,apuestaBase,rachaActual,fibonacci,fibIdx}=Capital;
  if(sistemaSel==='martingala'){
    const d=rachaActual<0?Math.abs(rachaActual):0;
    return apuestaBase*Math.pow(2,d);
  }
  if(sistemaSel==='fibonacci') return apuestaBase*(fibonacci[fibIdx]||1);
  if(sistemaSel==='paroli'){
    const v=rachaActual>0?Math.min(rachaActual,3):0;
    return apuestaBase*Math.pow(2,v);
  }
  if(sistemaSel==='d_alembert'){
    const adj=rachaActual<0?Math.abs(rachaActual):0;
    return Math.max(apuestaBase,apuestaBase+adj*apuestaBase);
  }
  return apuestaBase; // plano
}

function renderCapital() {
  const cont=$id('capital-panel'); if(!cont) return;
  const apSig=calcApuestaSiguiente(), maxAp=Capital.saldo*0.5;
  const apReal=Math.min(apSig,maxAp), riesgo=(apReal/Math.max(Capital.saldo,1))*100;

  cont.innerHTML=`
    <div style="display:grid;grid-template-columns:1fr 1fr;gap:14px">
      <div>
        <div class="capital-controls">
          <div class="cap-row"><span class="cap-label">SALDO ACTUAL ($)</span>
            <input type="number" id="cap-saldo" class="cap-input" value="${Capital.saldo}" min="0"/></div>
          <div class="cap-row"><span class="cap-label">APUESTA BASE ($)</span>
            <input type="number" id="cap-base" class="cap-input" value="${Capital.apuestaBase}" min="1"/></div>
          <div class="cap-row"><span class="cap-label">SISTEMA</span>
            <select id="cap-sistema" class="cap-select">
              <option value="martingala" ${Capital.sistemaSel==='martingala'?'selected':''}>Martingala</option>
              <option value="fibonacci"  ${Capital.sistemaSel==='fibonacci' ?'selected':''}>Fibonacci</option>
              <option value="paroli"     ${Capital.sistemaSel==='paroli'    ?'selected':''}>Paroli</option>
              <option value="d_alembert" ${Capital.sistemaSel==='d_alembert'?'selected':''}>D'Alembert</option>
              <option value="plano"      ${Capital.sistemaSel==='plano'     ?'selected':''}>Plana</option>
            </select></div>
          <div class="cap-row"><span class="cap-label">RACHA ACTUAL</span>
            <span class="cap-value ${Capital.rachaActual>=0?'cap-ganando':'cap-perdiendo'}">
              ${Capital.rachaActual>=0?'▲ +'+Capital.rachaActual:'▼ '+Capital.rachaActual}</span></div>
        </div>
        <div class="capital-result">
          <div class="cap-result-label">PRÓXIMA APUESTA SUGERIDA</div>
          <div class="cap-result-value" style="color:${riesgo>20?'var(--red)':riesgo>10?'var(--amber)':'var(--green)'}">
            $${apReal.toFixed(2)}<span class="cap-result-pct">(${riesgo.toFixed(1)}% saldo)</span></div>
          ${riesgo>20?'<div class="cap-warning">⚠ Riesgo alto — reduce apuesta base</div>':''}
        </div>
        <div class="capital-actions">
          <button class="cap-btn cap-btn-win" id="cap-win">✓ GANÓ</button>
          <button class="cap-btn cap-btn-lose" id="cap-lose">✗ PERDIÓ</button>
          <button class="cap-btn cap-btn-reset" id="cap-reset-btn">↺</button>
        </div>
      </div>
      <div>
        <div class="cap-info-grid">
          <div class="cap-info-block"><span class="cap-info-label">SISTEMA</span><span class="cap-info-val">${Capital.sistemaSel.toUpperCase()}</span></div>
          <div class="cap-info-block"><span class="cap-info-label">RONDAS</span><span class="cap-info-val">${Capital.histCapital.length-1}</span></div>
          <div class="cap-info-block"><span class="cap-info-label">P/L NETO</span>
            <span class="cap-info-val" style="color:${Capital.saldo-Capital.histCapital[0]>=0?'var(--green)':'var(--red)'}">
              ${Capital.saldo-Capital.histCapital[0]>=0?'+':''}$${(Capital.saldo-Capital.histCapital[0]).toFixed(0)}</span></div>
          <div class="cap-info-block"><span class="cap-info-label">MAX PÉRD. (5 series)</span>
            <span class="cap-info-val" style="color:var(--red)">$${(Capital.apuestaBase*(Capital.sistemaSel==='martingala'?Math.pow(2,5)-1:5)).toFixed(0)}</span></div>
        </div>
        <div class="capital-history" style="margin-top:12px">
          <div class="cap-hist-title">CURVA DE CAPITAL (últimas 20 rondas)</div>
          <div id="cap-hist-chart" style="margin-top:8px"></div>
        </div>
      </div>
    </div>`;

  renderCapitalChart();

  $id('cap-saldo')?.addEventListener('change', e=>{ Capital.saldo=parseFloat(e.target.value)||1000; renderCapital(); });
  $id('cap-base')?.addEventListener('change',  e=>{ Capital.apuestaBase=parseFloat(e.target.value)||10; renderCapital(); });
  $id('cap-sistema')?.addEventListener('change', e=>{ Capital.sistemaSel=e.target.value; renderCapital(); });
  $id('cap-win')?.addEventListener('click', ()=>{
    const ap=Math.min(calcApuestaSiguiente(),Capital.saldo*0.5);
    Capital.saldo=parseFloat((Capital.saldo+ap).toFixed(2));
    Capital.rachaActual=Capital.rachaActual<0?1:Capital.rachaActual+1;
    if(Capital.sistemaSel==='fibonacci'&&Capital.fibIdx>0) Capital.fibIdx--;
    Capital.histCapital.push(Capital.saldo);
    renderCapital(); showToast('✓ Victoria registrada','success');
  });
  $id('cap-lose')?.addEventListener('click', ()=>{
    const ap=Math.min(calcApuestaSiguiente(),Capital.saldo*0.5);
    Capital.saldo=parseFloat(Math.max(0,Capital.saldo-ap).toFixed(2));
    Capital.rachaActual=Capital.rachaActual>0?-1:Capital.rachaActual-1;
    if(Capital.sistemaSel==='fibonacci'){
      Capital.fibIdx++;
      if(Capital.fibIdx>=Capital.fibonacci.length)
        Capital.fibonacci.push(Capital.fibonacci.at(-1)+Capital.fibonacci.at(-2));
    }
    Capital.histCapital.push(Capital.saldo);
    renderCapital(); showToast('✗ Pérdida registrada','error');
  });
  $id('cap-reset-btn')?.addEventListener('click', ()=>{
    Capital.saldo=1000; Capital.apuestaBase=10; Capital.rachaActual=0;
    Capital.histCapital=[1000]; Capital.fibonacci=[1,1]; Capital.fibIdx=0;
    renderCapital(); showToast('Capital reiniciado','info');
  });
}

function renderCapitalChart() {
  const cont=$id('cap-hist-chart'); if(!cont) return;
  const data=Capital.histCapital.slice(-20);
  if(data.length<2){ cont.innerHTML='<span style="font-family:var(--font-mono);font-size:10px;color:var(--text-dim)">Sin historial aún</span>'; return; }
  const mn=Math.min(...data), mx=Math.max(...data), range=mx-mn||1;
  const W=300, H=65;
  const pts=data.map((v,i)=>{
    const x=4+(i/(data.length-1))*(W-8);
    const y=H-4-((v-mn)/range)*(H-8);
    return `${x},${y}`;
  }).join(' ');
  const color=data.at(-1)>=data[0]?'#10B981':'#EF4444';
  cont.innerHTML=`<svg width="${W}" height="${H}" style="overflow:visible;display:block">
    <polyline points="${pts}" fill="none" stroke="${color}" stroke-width="1.5" stroke-linejoin="round"/>
    ${data.map((v,i)=>{const x=4+(i/(data.length-1))*(W-8),y=H-4-((v-mn)/range)*(H-8);return `<circle cx="${x}" cy="${y}" r="2.5" fill="${color}"/>`;}).join('')}
    <text x="0" y="${H}" font-family="JetBrains Mono" font-size="9" fill="#64748B">$${mn.toFixed(0)}</text>
    <text x="0" y="11"   font-family="JetBrains Mono" font-size="9" fill="#64748B">$${mx.toFixed(0)}</text>
  </svg>`;
}

/* ═══════════════════════════════════════
   RENDER — RESUMEN EJECUTIVO
   ═══════════════════════════════════════ */

function renderResumenEjecutivo() {
  const cont=$id('resumen-panel'); if(!cont) return;
  if(G.tiros<5){ cont.innerHTML='<div style="font-family:var(--font-mono);font-size:11px;color:var(--text-dim);padding:20px;text-align:center">Registra al menos 5 tiros para ver el resumen.</div>'; return; }

  function scoreDocena(d) {
    const data=G.docenas[d]; let sc=50;
    sc+=Math.min(25,data.aus*2);
    if(data.ema.e5>data.ema.e10) sc+=10;
    // AF: usar afMagnitud (ponderado multi-ventana) con clamping simétrico
    const afMag = data.afDetalle?.afMagnitud ?? data.af;
    sc += Math.max(-15, Math.min(15, afMag * 8));
    // Bonus si AF está acelerando
    if (data.afDetalle?.afTrend === 'acelerando')   sc += 8;
    if (data.afDetalle?.afTrend === 'desacelerando') sc -= 5;
    sc-=Math.min(20,(data.f.f10||0)*3);
    if(data.estadoNombre==='peligro')     sc+=15;
    if(data.estadoNombre==='advertencia') sc+=8;
    return Math.max(0,Math.min(100,Math.round(sc)));
  }

  const scores={D1:scoreDocena('D1'),D2:scoreDocena('D2'),D3:scoreDocena('D3')};
  const bestD=Object.entries(scores).sort((a,b)=>b[1]-a[1])[0];
  const racha=calcRacha(), ent=G.entropia.norm;

  cont.innerHTML=`
    <div class="resumen-grid">
      <div class="resumen-main">
        <div class="resumen-label">DOCENA RECOMENDADA</div>
        <div class="resumen-big" style="color:${DOCENA_COLORS[bestD[0]]}">${bestD[0]}</div>
        <div class="resumen-sub">Score: ${bestD[1]}/100</div>
        <div class="resumen-sub" style="margin-top:6px">${DOCENAS[bestD[0]].min}–${DOCENAS[bestD[0]].max}</div>
      </div>
      <div class="resumen-scores">
        ${['D1','D2','D3'].map(d=>{
          const sc=scores[d], col=sc>=70?'var(--green)':sc>=50?'var(--amber)':'var(--red)';
          return `<div class="rscore-row">
            <span class="rscore-label" style="color:${DOCENA_COLORS[d]}">${d}</span>
            <div class="rscore-track"><div class="rscore-fill" style="width:${sc}%;background:${col}"></div></div>
            <span class="rscore-val" style="color:${col}">${sc}</span>
          </div>`;
        }).join('')}
      </div>
    </div>

    <div class="resumen-indicadores">
      ${[
        ['TENDENCIA SESIÓN',   ent>90?'✓ Aleatoria':ent>75?'⚠ Leve sesgo':'⚡ Sesgada'],
        ['RACHA COLOR',        racha.color?racha.color.toUpperCase()+' ×'+racha.largo:'—'],
        ['ENTROPÍA',           ent.toFixed(1)+'%'],
        ['SEÑALES ACTIVAS',    String(G.senales.length)],
        ['CHI²',               G.chi.valor.toFixed(1)+' (gl=36)'],
        ['ESTADO D1',          G.docenas.D1.estadoNombre.toUpperCase()],
        ['ESTADO D2',          G.docenas.D2.estadoNombre.toUpperCase()],
        ['ESTADO D3',          G.docenas.D3.estadoNombre.toUpperCase()],
        ['AUSENCIA D1',        G.docenas.D1.aus+' tiros'],
        ['AUSENCIA D2',        G.docenas.D2.aus+' tiros'],
        ['AUSENCIA D3',        G.docenas.D3.aus+' tiros'],
        ['CICLO PROM. D1',     G.docenas.D1.ciclo?G.docenas.D1.ciclo.toFixed(1)+' tiros':'—'],
        ['CICLO PROM. D2',     G.docenas.D2.ciclo?G.docenas.D2.ciclo.toFixed(1)+' tiros':'—'],
        ['CICLO PROM. D3',     G.docenas.D3.ciclo?G.docenas.D3.ciclo.toFixed(1)+' tiros':'—'],
        ['TOTAL TIROS',        String(G.tiros)],
        ['ROJOS / NEGROS',     G.color.rojo+' / '+G.color.negro],
      ].map(([l,v])=>`<div class="ri-item"><span class="ri-label">${l}</span><span class="ri-val">${v}</span></div>`).join('')}
    </div>

    <div class="resumen-top-senales">
      <div class="ri-label" style="margin-bottom:8px">TOP SEÑALES ACTIVAS</div>
      ${G.senales.slice(0,4).map(s=>`<div class="resumen-senal">
        <span>${s.icon}</span>
        <span style="font-family:var(--font-mono);font-size:10px;flex:1">${s.titulo}</span>
        <span style="font-family:var(--font-mono);font-size:10px;color:var(--cyan)">${s.conf?s.conf+'%':''}</span>
      </div>`).join('')}
      ${!G.senales.length?'<div class="empty-msg" style="padding:8px 0">Sin señales aún.</div>':''}
    </div>`;
}

/* ═══════════════════════════════════════
   RENDER — HEADER + CAPTURA
   ═══════════════════════════════════════ */

function renderHeader() {
  setText('m-tiros',G.tiros);
  const st=$id('m-status');
  if(st){ st.textContent=G.tiros>=10?'ANALIZANDO':G.tiros>0?'CALIBRANDO':'ESPERANDO'; st.className=G.tiros>=10?'status-active':G.tiros>0?'status-warning':'status-idle'; }
  setText('m-session',G.tiros>0?`${G.tiros} TIROS`:'NUEVA');
}

function renderLastNumber(n) {
  const el=$id('last-number'), badge=$id('last-color-badge'); if(!el||!badge) return;
  el.textContent=n; el.classList.remove('flash'); void el.offsetWidth; el.classList.add('flash');
  const color=colorNum(n); badge.textContent=color.toUpperCase(); badge.className=`last-color-badge ${color}`;
}

function renderRachas() {
  const rc=calcRacha(), rd=calcRachaDocena();
  const elC=$id('streak-value');
  if(elC) elC.textContent=rc.largo>1?(rc.color==='rojo'?'🔴':rc.color==='negro'?'⚫':'🟢')+` ×${rc.largo}`:'—';
  const elD=$id('streak-docena');
  if(elD) elD.textContent=rd.doc&&rd.largo>1?`${rd.doc} ×${rd.largo}`:'—';
}

function renderHistoryStrip() {
  const cont=$id('history-strip'); if(!cont) return;
  cont.innerHTML=[...historial].slice(-24).reverse().map((n,i)=>{
    const color=colorNum(n), cls=n===0?'hchip-0':`hchip-${color}`;
    return `<span class="hchip ${cls} ${i===0?'newest':''}">${n}</span>`;
  }).join('');
}

/* ═══════════════════════════════════════
   RENDER — HISTORIAL
   ═══════════════════════════════════════ */

function renderHistorial(filtroNum='', filtroTipo='all') {
  const cont=$id('historial-scroll'); if(!cont) return;
  let datos=historial.map((n,i)=>({n,i:i+1})).reverse();
  if(filtroNum.trim()!==''){const f=parseInt(filtroNum); if(!isNaN(f)) datos=datos.filter(d=>d.n===f);}
  if(filtroTipo!=='all') datos=datos.filter(d=>{
    if(filtroTipo==='D1') return d.n>=1&&d.n<=12;
    if(filtroTipo==='D2') return d.n>=13&&d.n<=24;
    if(filtroTipo==='D3') return d.n>=25&&d.n<=36;
    if(filtroTipo==='rojo')  return NUMEROS_ROJOS.has(d.n);
    if(filtroTipo==='negro') return d.n!==0&&!NUMEROS_ROJOS.has(d.n);
    if(filtroTipo==='0')     return d.n===0;
    return true;
  });
  if(!datos.length){ cont.innerHTML='<div class="empty-msg">Sin resultados.</div>'; return; }
  cont.innerHTML=datos.map((d,idx)=>{
    const color=colorNum(d.n), doc=docenaDeNum(d.n), col=columnaDeNum(d.n)||'—';
    const par=d.n===0?'—':d.n%2===0?'PAR':'IMP';
    const emoji=color==='rojo'?'🔴':color==='negro'?'⚫':'🟢';
    return `<div class="hist-row ${idx===0?'newest':''}">
      <span class="hist-idx">#${d.i}</span>
      <span class="hist-num ${color}">${d.n}</span>
      <span class="hist-doc">${doc}</span>
      <span class="hist-col">${col}</span>
      <span class="hist-par">${par}</span>
      <span>${emoji}</span>
    </div>`;
  }).join('');
  setText('hist-count',`${historial.length} tiros`);
}

/* ═══════════════════════════════════════
   RENDER ALL
   ═══════════════════════════════════════ */

function renderAll() {
  renderHeader();
  renderRachas();
  renderHistoryStrip();
  renderDocenas();
  renderEMA();
  renderAF();
  renderCicloCanvas();
  renderZonas();
  renderFreqChart();
  renderSenales();
  renderProbabilidades();
  renderAlertsLog();
  renderEstadisticas();
  renderApuestas();
  renderVecinos();
  renderPatrones();
  renderCapital();
  renderResumenEjecutivo();
  renderHistorial($id('hist-search')?.value||'', $id('hist-filter')?.value||'all');
}

/* ═══════════════════════════════════════
   REGISTRO DE NÚMERO
   ═══════════════════════════════════════ */

/* ══════════════════════════════════════════════════════════════
   REGISTRO DE NÚMERO
   Semáforo real: _lock se activa al entrar y solo se libera
   en el siguiente frame de animación (requestAnimationFrame),
   garantizando que cualquier evento duplicado que llegue en
   el mismo tick o en frames intermedios sea descartado.
   Sin blur/focus: eliminamos el ciclo de re-entrega de eventos.
   ══════════════════════════════════════════════════════════════ */
let _lock = false;

function registrarNumero(rawVal) {
  // Semáforo: descarta cualquier llamada mientras se está procesando
  if (_lock) return false;
  _lock = true;

  // Capturar valor ANTES de limpiar (para qbtn que pasan número directo)
  const inp = $id('numero-input');
  const valorCapturado = (rawVal !== undefined && rawVal !== null && String(rawVal).trim() !== '')
    ? String(rawVal)
    : (inp ? inp.value : '');

  // Limpiar input inmediatamente — sin blur ni focus
  if (inp) inp.value = '';

  // Validar
  const n = parseInt(valorCapturado, 10);
  if (isNaN(n) || n < 0 || n > 36) {
    if (valorCapturado.trim() !== '') {
      showToast('Número inválido. Usa 0–36', 'error');
      if (inp) { inp.classList.add('invalid'); setTimeout(() => inp.classList.remove('invalid'), 500); }
    }
    // Liberar lock en el siguiente frame
    requestAnimationFrame(() => { _lock = false; });
    return false;
  }

  // Registrar
  historial.push(n);
  recalcularTodo();
  renderLastNumber(n);
  renderAll();

  // Alertas automáticas
  if (n === 0) agregarAlerta(`CERO cayó en tiro #${G.tiros}`, 'warning');
  const doc = docenaDeNum(n);
  if (doc !== 'CERO') {
    if (G.docenas[doc].aus === 0 && historial.length > 5) {
      let prevAus = 0;
      for (let i = historial.length - 2; i >= 0; i--) { if (docenaDeNum(historial[i]) === doc) break; prevAus++; }
      if (prevAus >= 8) agregarAlerta(`${doc} reaparece tras ${prevAus} tiros de ausencia`, 'success');
    }
  }
  const rc = calcRacha();
  if (rc.largo === 5)  agregarAlerta(`Racha ${rc.color?.toUpperCase()} ×5 detectada`, 'warning');
  if (rc.largo === 8)  agregarAlerta(`⚠ Racha ${rc.color?.toUpperCase()} ×8 — ALERTA`, 'danger');
  if (rc.largo === 12) agregarAlerta(`🚨 Racha ${rc.color?.toUpperCase()} ×12 — EXTREMO`, 'danger');

  guardarStorage();

  // Liberar lock en el siguiente frame de animación
  // (garantiza que todos los eventos pendientes del frame actual sean descartados)
  requestAnimationFrame(() => { _lock = false; });
  return true;
}

function deshacerUltimo() {
  if(!historial.length){showToast('Sin tiros que deshacer','error');return;}
  const n=historial.pop(); recalcularTodo(); renderAll(); guardarStorage();
  showToast(`Deshecho: número ${n}`,'info');
}

/* ═══════════════════════════════════════
   BOTONES RÁPIDOS
   ═══════════════════════════════════════ */

function generarBotonesRapidos() {
  const cont=$id('quick-nums'); if(!cont) return;
  for(let n=0;n<=36;n++){
    const btn=document.createElement('button');
    btn.className=`qbtn qbtn-${colorNum(n)}`;
    btn.textContent=n;
    btn.addEventListener('click',()=>registrarNumero(n));
    cont.appendChild(btn);
  }
}

/* ═══════════════════════════════════════
   PERSISTENCIA
   ═══════════════════════════════════════ */

const SK='estrategico_pro_v3';

function guardarStorage() {
  try{ localStorage.setItem(SK,JSON.stringify(historial)); }catch(e){}
}

function cargarStorage() {
  try{
    const raw=localStorage.getItem(SK);
    if(!raw) return;
    const arr=JSON.parse(raw);
    if(Array.isArray(arr)&&arr.length){
      historial.push(...arr); recalcularTodo(); renderAll();
      showToast(`Sesión restaurada: ${historial.length} tiros`,'success');
    }
  }catch(e){}
}

function resetSesion() {
  if(!confirm('¿Reiniciar sesión? Se borrarán todos los datos.')) return;
  historial.length=0; G.alertsLog.length=0;
  localStorage.removeItem(SK);
  recalcularTodo(); renderAll();
  $id('last-number').textContent='—';
  $id('last-color-badge').textContent='—'; $id('last-color-badge').className='last-color-badge';
  $id('streak-value').textContent='—'; $id('streak-docena').textContent='—';
  $id('signal-banner').style.display='none';
  showToast('Sesión reiniciada','success');
}

/* ═══════════════════════════════════════
   EXPORTAR
   ═══════════════════════════════════════ */

function exportJSON() {
  if(!historial.length){showToast('Sin datos','error');return;}
  const payload={exportado:new Date().toISOString(),version:'3.0',tiros:historial.length,historial,docenas:G.docenas,chi:G.chi,entropia:G.entropia,color:G.color,paridad:G.paridad,mitades:G.mitades,columnas:G.columnas,zonas:G.zonas};
  dlFile('estrategico_pro.json',JSON.stringify(payload,null,2),'application/json');
  showToast('JSON exportado ✓','success');
}

function exportCSV() {
  if(!historial.length){showToast('Sin datos','error');return;}
  const header='tiro,numero,color,docena,columna,paridad,mitad';
  const rows=historial.map((n,i)=>{
    const col=columnaDeNum(n)||'—', par=n===0?'—':n%2===0?'PAR':'IMPAR', mit=n===0?'—':n<=18?'BAJA':'ALTA';
    return `${i+1},${n},${colorNum(n)},${docenaDeNum(n)},${col},${par},${mit}`;
  });
  dlFile('estrategico_pro.csv',[header,...rows].join('\n'),'text/csv');
  showToast('CSV exportado ✓','success');
}

function dlFile(nombre,contenido,tipo) {
  const blob=new Blob([contenido],{type:tipo}), url=URL.createObjectURL(blob), a=document.createElement('a');
  a.href=url; a.download=nombre; a.click(); URL.revokeObjectURL(url);
}

/* ═══════════════════════════════════════
   UI UTILITIES
   ═══════════════════════════════════════ */

let toastTimer;
function showToast(msg,tipo='') {
  const el=$id('toast'); if(!el) return;
  el.textContent=msg; el.className=`toast show ${tipo}`;
  clearTimeout(toastTimer); toastTimer=setTimeout(()=>{el.className='toast';},2800);
}

function actualizarReloj() {
  const el=$id('m-time'); if(el) el.textContent=new Date().toLocaleTimeString('es-CO');
}

/* ═══════════════════════════════════════
   TABS
   ═══════════════════════════════════════ */

function initTabs() {
  document.querySelectorAll('.tab').forEach(tab=>{
    tab.addEventListener('click',()=>{
      document.querySelectorAll('.tab').forEach(t=>t.classList.remove('active'));
      document.querySelectorAll('.tab-pane').forEach(p=>p.classList.remove('active'));
      tab.classList.add('active');
      const pane=$id('tab-'+tab.dataset.tab);
      if(pane) pane.classList.add('active');
      // Re-render canvas al cambiar tab
      if(tab.dataset.tab==='docenas') setTimeout(renderCicloCanvas,50);
    });
  });
}

/* ═══════════════════════════════════════
   INICIALIZACIÓN
   ═══════════════════════════════════════ */

document.addEventListener('DOMContentLoaded',()=>{
  initTabs();
  generarBotonesRapidos();

  const inp = $id('numero-input');
  if (inp) {
    // Solo permitir dígitos mientras se escribe
    inp.addEventListener('keypress', e => {
      if (!/[0-9]/.test(e.key) && e.key !== 'Enter') e.preventDefault();
    });

    // Enter: capturar valor y registrar
    // keydown garantiza que capturamos ANTES de que el browser haga cualquier otra cosa
    inp.addEventListener('keydown', e => {
      if (e.key === 'Enter') {
        e.preventDefault();
        e.stopImmediatePropagation(); // bloquea otros listeners del mismo elemento
        const val = inp.value.trim();
        registrarNumero(val);
      }
    });

    // Validación visual mientras escribe
    inp.addEventListener('input', () => {
      const v = parseInt(inp.value);
      inp.classList.toggle('invalid', inp.value !== '' && (isNaN(v) || v < 0 || v > 36));
    });
  }

  // Botón: tabIndex=-1 evita que reciba foco con Tab o click,
  // impidiendo que Enter "rebote" al botón después de salir del input
  const btnReg = $id('btn-registrar');
  if (btnReg) {
    btnReg.setAttribute('tabindex', '-1');
    btnReg.addEventListener('mousedown', e => {
      // mousedown en lugar de click: se ejecuta antes de que el input pierda foco
      // preventDefault evita que el input pierda foco (y así no se dispara blur)
      e.preventDefault();
      const val = inp ? inp.value.trim() : '';
      registrarNumero(val);
    });
  }
  $id('btn-undo')?.addEventListener('click',deshacerUltimo);
  $id('btn-export-json')?.addEventListener('click',exportJSON);
  $id('btn-export-csv')?.addEventListener('click',exportCSV);
  $id('btn-reset')?.addEventListener('click',resetSesion);
  $id('sb-close')?.addEventListener('click',()=>{ $id('signal-banner').style.display='none'; });
  $id('hist-search')?.addEventListener('input',e=>renderHistorial(e.target.value,$id('hist-filter')?.value));
  $id('hist-filter')?.addEventListener('change',e=>renderHistorial($id('hist-search')?.value,e.target.value));

  actualizarReloj();
  setInterval(actualizarReloj,1000);

  // Render capital en su tab al activarse
  $id('tab-capital') && document.querySelector('[data-tab="capital"]')?.addEventListener('click',()=>{ setTimeout(renderCapital,50); });

  cargarStorage();
  if(!historial.length){ recalcularTodo(); renderAll(); }

  console.log('%cESTRATÉGICO PRO v3.0 — Listo','color:#00D4FF;font-family:monospace;font-weight:bold');
});
