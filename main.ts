// tiny-stack-vm-01: interpreter for make.fun's tiny stack ISA (v1).
// One run answers a whole set: /input/<id>/{program,input}.bin in,
// /output/<id>/{stdout.bin,exit.txt} out. Node 22, no dependencies.
import {mkdirSync, readdirSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Opcode facts, packed as imm * 16 + pops * 4 + pushes + 1 (0 = no opcode).
const META = new Uint8Array(256);
for (const [op, imm, pops, pushes] of [
  [0x00,0,0,0],[0x01,1,0,1],[0x02,4,0,1],[0x03,0,1,0],
  [0x04,0,1,2],[0x05,0,2,2],[0x06,0,2,3],[0x07,0,3,3],
  [0x10,0,2,1],[0x11,0,2,1],[0x12,0,2,1],[0x13,0,2,1],
  [0x14,0,2,1],[0x15,0,2,1],[0x16,0,2,1],[0x17,0,1,1],
  [0x18,0,2,1],[0x19,0,2,1],[0x1a,0,2,1],[0x1b,0,1,1],
  [0x1c,0,2,1],[0x1d,0,2,1],[0x1e,0,2,1],[0x20,0,2,1],
  [0x21,0,2,1],[0x22,0,2,1],[0x30,2,0,0],[0x31,2,1,0],
  [0x32,2,1,0],[0x33,2,0,0],[0x34,0,0,0],[0x40,0,1,1],
  [0x41,0,2,0],[0x50,0,1,0],[0x51,0,1,0],[0x52,0,0,1],
  [0x53,0,1,0],
]) META[op] = imm * 16 + pops * 4 + pushes + 1;

const STEP_LIMIT = 1_000_000;
const OUT_LIMIT = 65_536;

function runProgram(prog: Uint8Array, input: Uint8Array): [Uint8Array, number] {
  const n = prog.length;
  const data = new Int32Array(256);
  const ret = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(OUT_LIMIT);
  let sp = 0, rp = 0, pc = 0, steps = 0, olen = 0, ipos = 0;
  const finish = (code: number): [Uint8Array, number] => [out.subarray(0, olen), code];
  for (;;) {
    if (steps === STEP_LIMIT) return finish(10);
    if (pc < 0 || pc >= n) return finish(9);
    const op = prog[pc];
    const packed = META[op];
    if (packed === 0) return finish(5);
    const fields = packed - 1;
    const imm = fields >> 4, pops = (fields >> 2) & 3, pushes = fields & 3;
    if (pc + imm >= n) return finish(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return finish(2);
    if (sp - pops + pushes > 256) return finish(3);
    pc = next;
    switch (op) {
      case 0x00: return finish(0);
      case 0x01: data[sp++] = (prog[next - 1] << 24) >> 24; break;
      case 0x02: data[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: data[sp] = data[sp - 1]; sp++; break;
      case 0x05: { const t = data[sp - 1]; data[sp - 1] = data[sp - 2]; data[sp - 2] = t; break; }
      case 0x06: data[sp] = data[sp - 2]; sp++; break;
      case 0x07: { const a = data[sp - 3]; data[sp - 3] = data[sp - 2]; data[sp - 2] = data[sp - 1]; data[sp - 1] = a; break; }
      case 0x17: data[sp - 1] = -data[sp - 1] | 0; break;
      case 0x1b: data[sp - 1] = ~data[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = data[sp - 1], a = data[sp - 2];
        let r = 0;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (b === 0) return finish(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 0x14) { if (b === 0) return finish(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 0x15) { if (b === 0) return finish(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (b === 0) return finish(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        data[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        if (op === 0x30) { pc = next + rel; break; }
        const v = data[--sp];
        const take = op === 0x31 ? v === 0 : v !== 0;
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (rp === 64) return finish(7);
        ret[rp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34:
        if (rp === 0) return finish(8);
        pc = ret[--rp];
        break;
      case 0x40: {
        const addr = data[sp - 1];
        if (addr < 0 || addr >= 256) return finish(6);
        data[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = data[sp - 1], v = data[sp - 2];
        if (addr < 0 || addr >= 256) return finish(6);
        sp -= 2;
        mem[addr] = v;
        break;
      }
      case 0x50: {
        const text = String(data[sp - 1]);
        if (olen + text.length > OUT_LIMIT) return finish(11);
        sp--;
        for (let i = 0; i < text.length; i++) out[olen++] = text.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > OUT_LIMIT) return finish(11);
        out[olen++] = data[--sp] & 255;
        break;
      case 0x52:
        data[sp++] = ipos < input.length ? input[ipos++] : -1;
        break;
      case 0x53:
        return finish(data[--sp] & 255);
    }
  }
}

for (const id of readdirSync(INPUT_DIR).sort()) {
  const prog = readFileSync(join(INPUT_DIR, id, 'program.bin'));
  const input = readFileSync(join(INPUT_DIR, id, 'input.bin'));
  const [bytes, code] = runProgram(prog, input);
  mkdirSync(join(OUTPUT_DIR, id), {recursive: true});
  writeFileSync(join(OUTPUT_DIR, id, 'stdout.bin'), bytes);
  writeFileSync(join(OUTPUT_DIR, id, 'exit.txt'), `${code}\n`);
}
