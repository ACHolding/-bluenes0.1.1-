#!/usr/bin/env python3
"""Blue NES 0.1 — a self-contained, silent, NTSC NROM emulator.

Python 3.9+ and Tkinter; no third-party packages. Run: python3 blue_nes.py
Optional: python3 blue_nes.py game.nes | --demo | --self-test | --headless N

Implements the NES 2A03's 151 official 6502 opcodes and stable undocumented
instructions; NROM iNES cartridges; background/sprite graphics and controllers.
The scanline renderer and instruction-granularity timing are approximate.
There is NO AUDIO synthesis, DMC, PAL, NES 2.0, save persistence, or mapper
bank-switching. CPU status/frame IRQ registers are partially implemented.
Use homebrew or ROMs you are entitled to use. No commercial ROMs are included.
The built-in demo is original and is assembled in memory, never written out.

Technical references: https://www.nesdev.org/wiki/CPU_unofficial_opcodes
https://www.nesdev.org/wiki/PPU_registers
https://www.nesdev.org/wiki/PPU_scrolling
https://www.nesdev.org/wiki/NROM
"""
from __future__ import annotations
import argparse
import pathlib
import sys
import time
import unittest

VERSION = '0.1'
WIDTH, HEIGHT = 256, 240
CPU_HZ = 1789773
OPAQUE_TABLE = b'\0' + b'\1'*255
GRAYSCALE_TABLE = bytes(i & 0x30 for i in range(256))
C, Z, I, D, B, U, V, N = 1, 2, 4, 8, 16, 32, 64, 128

# Conventional 2C02 approximation; no claim of exact analog color reproduction.
PALETTE = tuple(bytes.fromhex(x) for x in (
    '666666 002A88 1412A7 3B00A4 5C007E 6E0040 6C0700 561D00 '
    '333500 0B4800 005200 004F08 00404D 000000 000000 000000 '
    'ADADAD 155FD9 4240FF 7527FE A01ACC B71E7B B53120 994E00 '
    '6B6D00 388700 0C9300 008F32 007C8D 000000 000000 000000 '
    'FFFEFF 64B0FF 9290FF C676FF F36AFF FE6ECC FE8170 EA9E22 '
    'BCBE00 88D800 5CE430 45E082 48CDDE 4F4F4F 000000 000000 '
    'FFFEFF C0DFFF D3D2FF E8C8FF FBC2FF FEC4EA FECCC5 F7D8A5 '
    'E4E594 CFEF96 BDF4AB B3F3CC B5EBF2 B8B8B8 000000 000000'
).split())

class ROMError(ValueError):
    """Invalid or unsupported cartridge format."""

class CPUError(RuntimeError):
    """A CPU jam or unstable instruction cannot be continued safely."""

class Cartridge:
    MAX_SIZE = 1024 * 1024

    def __init__(self, data: bytes, name='Cartridge'):
        if len(data) > self.MAX_SIZE:
            raise ROMError('File is too large for NROM (maximum accepted: 1 MiB).')
        if len(data) < 16 or data[:4] != b'NES\x1a':
            raise ROMError('Not an iNES .nes ROM. ZIP files must be extracted first.')
        h = data[:16]
        if h[7] & 12 == 8:
            raise ROMError('NES 2.0 headers are not supported. Use an iNES NROM ROM.')
        if h[7] & 3:
            raise ROMError('VS System and PlayChoice cartridges are not supported.')
        self.mapper = (h[6] >> 4) | (h[7] & 0xf0)
        if self.mapper != 0:
            raise ROMError(f'Mapper {self.mapper} is not supported. This build supports mapper 0 / NROM only.')
        if h[4] not in (1, 2) or h[5] not in (0, 1):
            raise ROMError('NROM requires 16/32 KiB PRG and 0/8 KiB CHR.')
        if h[9] & 1:
            raise ROMError('PAL timing is not supported. Choose an NTSC ROM.')
        if h[10] & 3 == 2:
            raise ROMError('This ROM requests PAL timing; this build is NTSC only.')
        self.name = name
        self.battery = bool(h[6] & 2)
        self.mirroring = 'four-screen' if h[6] & 8 else ('vertical' if h[6] & 1 else 'horizontal')
        start = 16 + (512 if h[6] & 4 else 0)
        end = start + h[4] * 16384
        total = end + h[5] * 8192
        if len(data) < total:
            raise ROMError(f'Truncated ROM: expected at least {total:,} bytes, got {len(data):,}.')
        self.prg = bytes(data[start:end])
        self.chr_ram = h[5] == 0
        self.chr = bytearray(8192) if self.chr_ram else bytearray(data[end:total])
        self.ram = bytearray(8192)  # Volatile only; no save files are written.
        if h[6] & 4:
            self.ram[0x1000:0x1200] = data[16:528]

    def read(self, address):
        if address >= 0x8000:
            return self.prg[(address - 0x8000) % len(self.prg)]
        if address >= 0x6000:
            return self.ram[address - 0x6000]
        return 0

    def write(self, address, value):
        if 0x6000 <= address < 0x8000:
            self.ram[address - 0x6000] = value

class Controller:
    """Serial A, B, Select, Start, Up, Down, Left, Right shift register."""
    def __init__(self):
        self.buttons = 0
        self.latch = 0
        self.strobe = 0
        self.index = 0

    def write(self, value):
        value &= 1
        if self.strobe or value:
            self.latch = self.buttons
            self.index = 0
        self.strobe = value

    def read(self):
        if self.strobe:
            return self.buttons & 1
        if self.index >= 8:
            return 1
        out = (self.latch >> self.index) & 1
        self.index += 1
        return out

    def set(self, button, pressed):
        if pressed:
            self.buttons |= 1 << button
        else:
            self.buttons &= ~(1 << button)
        if self.strobe:
            self.latch = self.buttons

# Every byte has an explicit decoding entry; '+' means read page-cross penalty.
# JAM intentionally stops instead of accidentally running arbitrary bytes as NOP.
OPCODE_ROWS = '''
BRK:imp:7 ORA:izx:6 JAM:imp:2 SLO:izx:8 NOP:zp:3 ORA:zp:3 ASL:zp:5 SLO:zp:5 PHP:imp:3 ORA:imm:2 ASL:acc:2 ANC:imm:2 NOP:abs:4 ORA:abs:4 ASL:abs:6 SLO:abs:6
BPL:rel:2 ORA:izy:5+ JAM:imp:2 SLO:izy:8 NOP:zpx:4 ORA:zpx:4 ASL:zpx:6 SLO:zpx:6 CLC:imp:2 ORA:aby:4+ NOP:imp:2 SLO:aby:7 NOP:abx:4+ ORA:abx:4+ ASL:abx:7 SLO:abx:7
JSR:abs:6 AND:izx:6 JAM:imp:2 RLA:izx:8 BIT:zp:3 AND:zp:3 ROL:zp:5 RLA:zp:5 PLP:imp:4 AND:imm:2 ROL:acc:2 ANC:imm:2 BIT:abs:4 AND:abs:4 ROL:abs:6 RLA:abs:6
BMI:rel:2 AND:izy:5+ JAM:imp:2 RLA:izy:8 NOP:zpx:4 AND:zpx:4 ROL:zpx:6 RLA:zpx:6 SEC:imp:2 AND:aby:4+ NOP:imp:2 RLA:aby:7 NOP:abx:4+ AND:abx:4+ ROL:abx:7 RLA:abx:7
RTI:imp:6 EOR:izx:6 JAM:imp:2 SRE:izx:8 NOP:zp:3 EOR:zp:3 LSR:zp:5 SRE:zp:5 PHA:imp:3 EOR:imm:2 LSR:acc:2 ALR:imm:2 JMP:abs:3 EOR:abs:4 LSR:abs:6 SRE:abs:6
BVC:rel:2 EOR:izy:5+ JAM:imp:2 SRE:izy:8 NOP:zpx:4 EOR:zpx:4 LSR:zpx:6 SRE:zpx:6 CLI:imp:2 EOR:aby:4+ NOP:imp:2 SRE:aby:7 NOP:abx:4+ EOR:abx:4+ LSR:abx:7 SRE:abx:7
RTS:imp:6 ADC:izx:6 JAM:imp:2 RRA:izx:8 NOP:zp:3 ADC:zp:3 ROR:zp:5 RRA:zp:5 PLA:imp:4 ADC:imm:2 ROR:acc:2 ARR:imm:2 JMP:ind:5 ADC:abs:4 ROR:abs:6 RRA:abs:6
BVS:rel:2 ADC:izy:5+ JAM:imp:2 RRA:izy:8 NOP:zpx:4 ADC:zpx:4 ROR:zpx:6 RRA:zpx:6 SEI:imp:2 ADC:aby:4+ NOP:imp:2 RRA:aby:7 NOP:abx:4+ ADC:abx:4+ ROR:abx:7 RRA:abx:7
NOP:imm:2 STA:izx:6 NOP:imm:2 SAX:izx:6 STY:zp:3 STA:zp:3 STX:zp:3 SAX:zp:3 DEY:imp:2 NOP:imm:2 TXA:imp:2 XAA:imm:2 STY:abs:4 STA:abs:4 STX:abs:4 SAX:abs:4
BCC:rel:2 STA:izy:6 JAM:imp:2 AHX:izy:6 STY:zpx:4 STA:zpx:4 STX:zpy:4 SAX:zpy:4 TYA:imp:2 STA:aby:5 TXS:imp:2 TAS:aby:5 SHY:abx:5 STA:abx:5 SHX:aby:5 AHX:aby:5
LDY:imm:2 LDA:izx:6 LDX:imm:2 LAX:izx:6 LDY:zp:3 LDA:zp:3 LDX:zp:3 LAX:zp:3 TAY:imp:2 LDA:imm:2 TAX:imp:2 LXA:imm:2 LDY:abs:4 LDA:abs:4 LDX:abs:4 LAX:abs:4
BCS:rel:2 LDA:izy:5+ JAM:imp:2 LAX:izy:5+ LDY:zpx:4 LDA:zpx:4 LDX:zpy:4 LAX:zpy:4 CLV:imp:2 LDA:aby:4+ TSX:imp:2 LAS:aby:4+ LDY:abx:4+ LDA:abx:4+ LDX:aby:4+ LAX:aby:4+
CPY:imm:2 CMP:izx:6 NOP:imm:2 DCP:izx:8 CPY:zp:3 CMP:zp:3 DEC:zp:5 DCP:zp:5 INY:imp:2 CMP:imm:2 DEX:imp:2 AXS:imm:2 CPY:abs:4 CMP:abs:4 DEC:abs:6 DCP:abs:6
BNE:rel:2 CMP:izy:5+ JAM:imp:2 DCP:izy:8 NOP:zpx:4 CMP:zpx:4 DEC:zpx:6 DCP:zpx:6 CLD:imp:2 CMP:aby:4+ NOP:imp:2 DCP:aby:7 NOP:abx:4+ CMP:abx:4+ DEC:abx:7 DCP:abx:7
CPX:imm:2 SBC:izx:6 NOP:imm:2 ISC:izx:8 CPX:zp:3 SBC:zp:3 INC:zp:5 ISC:zp:5 INX:imp:2 SBC:imm:2 NOP:imp:2 SBC:imm:2 CPX:abs:4 SBC:abs:4 INC:abs:6 ISC:abs:6
BEQ:rel:2 SBC:izy:5+ JAM:imp:2 ISC:izy:8 NOP:zpx:4 SBC:zpx:4 INC:zpx:6 ISC:zpx:6 SED:imp:2 SBC:aby:4+ NOP:imp:2 ISC:aby:7 NOP:abx:4+ SBC:abx:4+ INC:abx:7 ISC:abx:7
'''
OPS = []
for _entry in OPCODE_ROWS.split():
    _op, _mode, _cycles = _entry.split(':')
    OPS.append((_op, _mode, int(_cycles.rstrip('+')), _cycles.endswith('+')))
assert len(OPS) == 256

class CPU:
    def __init__(self, bus):
        self.bus = bus
        self.a = self.x = self.y = 0
        self.s = 0xfd
        self.p = I | U
        self.pc = 0
        self.cycles = 0
        self.nmi_pending = False
        self.irq_mask_once = None
        self.halted = False

    def reset(self):
        self.a = self.x = self.y = 0
        self.s, self.p = 0xfd, I | U
        self.pc = self.bus.read(0xfffc) | self.bus.read(0xfffd) << 8
        self.cycles = 7
        self.nmi_pending = self.halted = False
        self.irq_mask_once = None

    def fetch(self):
        value = self.bus.read(self.pc)
        self.pc = (self.pc + 1) & 0xffff
        return value

    def push(self, value):
        self.bus.write(0x100 | self.s, value & 255)
        self.s = (self.s - 1) & 255

    def pull(self):
        self.s = (self.s + 1) & 255
        return self.bus.read(0x100 | self.s)

    def nz(self, value):
        value &= 255
        self.p = (self.p & ~(N | Z)) | (value & N) | (Z if value == 0 else 0)
        return value

    def flag(self, mask, enabled):
        self.p = (self.p | mask) if enabled else (self.p & ~mask)

    def adc(self, value):
        total = self.a + value + (self.p & C)
        self.flag(C, total > 255)
        self.flag(V, (~(self.a ^ value) & (self.a ^ total)) & 128)
        self.a = self.nz(total)  # The NES ignores decimal mode in ADC/SBC.

    def compare(self, reg, value):
        self.flag(C, reg >= value)
        self.nz(reg - value)

    def interrupt(self, vector):
        self.push(self.pc >> 8)
        self.push(self.pc)
        self.push((self.p | U) & ~B)
        self.p |= I
        self.pc = self.bus.read(vector) | self.bus.read(vector + 1) << 8
        self.cycles += 7
        return 7

    def step(self):
        if self.halted:
            raise CPUError('The CPU is halted; reset or load another ROM.')
        old_i = bool(self.p & I)
        irq_mask = old_i if self.irq_mask_once is None else self.irq_mask_once
        self.irq_mask_once = None
        if self.nmi_pending:
            self.nmi_pending = False
            return self.interrupt(0xfffa)
        if not irq_mask and getattr(self.bus, 'irq', False):
            return self.interrupt(0xfffe)
        origin = self.pc
        code = self.fetch()
        op, mode, cycles, penalty = OPS[code]
        if op in ('JAM', 'XAA', 'AHX', 'TAS', 'SHY', 'SHX', 'LXA'):
            self.halted = True
            kind = 'CPU JAM' if op == 'JAM' else 'Unsupported unstable opcode'
            raise CPUError(f'{kind} ${code:02X} ({op}) at ${origin:04X}. Reset or try another NROM ROM.')
        address = None
        crossed = False
        if mode == 'imm':
            address = self.pc
            self.pc = (self.pc + 1) & 0xffff
        elif mode in ('zp', 'zpx', 'zpy'):
            base = self.fetch()
            address = (base + (self.x if mode == 'zpx' else self.y if mode == 'zpy' else 0)) & 255
        elif mode in ('abs', 'abx', 'aby', 'ind'):
            base = self.fetch() | self.fetch() << 8
            address = base
            if mode in ('abx', 'aby'):
                address = (base + (self.x if mode == 'abx' else self.y)) & 0xffff
                crossed = (base ^ address) & 0xff00 != 0
            elif mode == 'ind':
                # NMOS 6502 JMP ($xxFF) wraps inside the pointer's page.
                address = self.bus.read(base) | self.bus.read((base & 0xff00) | ((base + 1) & 255)) << 8
        elif mode == 'izx':
            zp = (self.fetch() + self.x) & 255
            address = self.bus.read(zp) | self.bus.read((zp + 1) & 255) << 8
        elif mode == 'izy':
            zp = self.fetch()
            base = self.bus.read(zp) | self.bus.read((zp + 1) & 255) << 8
            address = (base + self.y) & 0xffff
            crossed = (base ^ address) & 0xff00 != 0
        elif mode == 'rel':
            offset = self.fetch()
            address = (self.pc + (offset if offset < 128 else offset - 256)) & 0xffff
        cycles += int(penalty and crossed)
        if mode == 'rel':
            condition = bool(self.p & (N,V,C,Z)[code >> 6]) == bool(code & 0x20)
            if condition:
                cycles += 1 + int((self.pc ^ address) & 0xff00 != 0)
                self.pc = address
        elif op in ('STA', 'STX', 'STY', 'SAX'):
            self.bus.write(address, {'STA': self.a, 'STX': self.x, 'STY': self.y, 'SAX': self.a & self.x}[op])
        elif op in ('ASL', 'LSR', 'ROL', 'ROR', 'INC', 'DEC', 'SLO', 'SRE', 'RLA', 'RRA', 'DCP', 'ISC'):
            value = self.a if mode == 'acc' else self.bus.read(address)
            original = value
            carry = self.p & C
            if op in ('ASL', 'SLO', 'ROL', 'RLA'):
                self.flag(C, value & 128)
                value = (value << 1) | (carry if op in ('ROL', 'RLA') else 0)
            elif op in ('LSR', 'SRE', 'ROR', 'RRA'):
                self.flag(C, value & 1)
                value = (value >> 1) | (carry << 7 if op in ('ROR', 'RRA') else 0)
            else:
                value += 1 if op in ('INC', 'ISC') else -1
            value = self.nz(value)
            if mode == 'acc':
                self.a = value
            else:
                self.bus.write(address, original)  # NMOS read/modify/write bus write.
                self.bus.write(address, value)
            if op == 'SLO': self.a = self.nz(self.a | value)
            elif op == 'SRE': self.a = self.nz(self.a ^ value)
            elif op == 'RLA': self.a = self.nz(self.a & value)
            elif op == 'RRA': self.adc(value)
            elif op == 'DCP': self.compare(self.a, value)
            elif op == 'ISC': self.adc(value ^ 255)
        elif op in ('LDA', 'LDX', 'LDY', 'LAX', 'LAS', 'ORA', 'AND', 'EOR', 'ADC', 'SBC', 'CMP', 'CPX', 'CPY', 'BIT', 'ANC', 'ALR', 'ARR', 'AXS'):
            value = self.bus.read(address)
            if op == 'LDA': self.a = self.nz(value)
            elif op == 'LDX': self.x = self.nz(value)
            elif op == 'LDY': self.y = self.nz(value)
            elif op == 'LAX': self.a = self.x = self.nz(value)
            elif op == 'LAS': self.a = self.x = self.s = self.nz(value & self.s)
            elif op == 'ORA': self.a = self.nz(self.a | value)
            elif op == 'AND': self.a = self.nz(self.a & value)
            elif op == 'EOR': self.a = self.nz(self.a ^ value)
            elif op == 'ADC': self.adc(value)
            elif op == 'SBC': self.adc(value ^ 255)
            elif op == 'CMP': self.compare(self.a, value)
            elif op == 'CPX': self.compare(self.x, value)
            elif op == 'CPY': self.compare(self.y, value)
            elif op == 'BIT': self.p = (self.p & ~(N | V | Z)) | (value & (N | V)) | (Z if not self.a & value else 0)
            elif op == 'ANC':
                self.a = self.nz(self.a & value)
                self.flag(C, self.a & 128)
            elif op == 'ALR':
                value &= self.a
                self.flag(C, value & 1)
                self.a = self.nz(value >> 1)
            elif op == 'ARR':
                value &= self.a
                self.a = self.nz((value >> 1) | ((self.p & C) << 7))
                self.flag(C, self.a & 64)
                self.flag(V, ((self.a >> 6) ^ (self.a >> 5)) & 1)
            elif op == 'AXS':
                value2 = self.a & self.x
                self.flag(C, value2 >= value)
                self.x = self.nz(value2 - value)
        elif op == 'JMP': self.pc = address
        elif op == 'JSR':
            ret = (self.pc - 1) & 0xffff
            self.push(ret >> 8); self.push(ret)
            self.pc = address
        elif op == 'RTS': self.pc = ((self.pull() | self.pull() << 8) + 1) & 0xffff
        elif op == 'RTI':
            self.p = (self.pull() | U) & ~B
            self.pc = self.pull() | self.pull() << 8
        elif op == 'BRK':
            self.pc = (self.pc + 1) & 0xffff
            self.push(self.pc >> 8); self.push(self.pc); self.push(self.p | B | U)
            self.p |= I
            self.pc = self.bus.read(0xfffe) | self.bus.read(0xffff) << 8
        elif op == 'PHA': self.push(self.a)
        elif op == 'PHP': self.push(self.p | B | U)
        elif op == 'PLA': self.a = self.nz(self.pull())
        elif op == 'PLP':
            self.p = (self.pull() | U) & ~B
            self.irq_mask_once = old_i
        elif op == 'TAX': self.x = self.nz(self.a)
        elif op == 'TAY': self.y = self.nz(self.a)
        elif op == 'TXA': self.a = self.nz(self.x)
        elif op == 'TYA': self.a = self.nz(self.y)
        elif op == 'TSX': self.x = self.nz(self.s)
        elif op == 'TXS': self.s = self.x
        elif op == 'INX': self.x = self.nz(self.x + 1)
        elif op == 'INY': self.y = self.nz(self.y + 1)
        elif op == 'DEX': self.x = self.nz(self.x - 1)
        elif op == 'DEY': self.y = self.nz(self.y - 1)
        elif op in ('CLC', 'SEC', 'CLI', 'SEI', 'CLV', 'CLD', 'SED'):
            mask = {'CLC': C, 'SEC': C, 'CLI': I, 'SEI': I, 'CLV': V, 'CLD': D, 'SED': D}[op]
            self.flag(mask, op in ('SEC', 'SEI', 'SED'))
            if op in ('CLI', 'SEI'): self.irq_mask_once = old_i
        elif op == 'NOP':
            if address is not None: self.bus.read(address)
        else:
            raise AssertionError(f'Unimplemented opcode {op}')
        self.p = (self.p | U) & ~B
        self.cycles += cycles
        return cycles

class SilentAPU:
    """Frame IRQ and length-counter status only. No sound or DMC emulation."""
    LENGTH = (10,254,20,2,40,4,80,6,160,8,60,10,14,12,26,14,
              12,16,24,18,48,20,96,22,192,24,72,26,16,28,32,30)
    def __init__(self):
        self.regs = bytearray(24)
        self.lengths = [0]*4
        self.enabled = 0
        self.mode5 = False
        self.inhibit = False
        self.frame_irq = False
        self.clock = 0
        self.half_clock = 0

    def write(self, address, value):
        if 0x4000 <= address <= 0x4013:
            self.regs[address - 0x4000] = value
            if address in (0x4003, 0x4007, 0x400b, 0x400f):
                channel = (address - 0x4003)//4
                if self.enabled & (1 << channel):
                    self.lengths[channel] = self.LENGTH[value >> 3]
        elif address == 0x4015:
            self.enabled = value & 15
            for i in range(4):
                if not self.enabled & (1 << i): self.lengths[i] = 0
        elif address == 0x4017:
            self.mode5 = bool(value & 128)
            self.inhibit = bool(value & 64)
            if self.inhibit: self.frame_irq = False
            self.clock = self.half_clock = 0
            if self.mode5: self.half_frame()

    def half_frame(self):
        for i in range(4):
            halt_mask = 128 if i == 2 else 32
            if self.lengths[i] and not self.regs[i*4] & halt_mask:
                self.lengths[i] -= 1

    def tick(self, cycles):
        old = self.clock
        self.clock += cycles
        events = (14913, 37281) if self.mode5 else (14913, 29829)
        for point in events:
            if old < point <= self.clock: self.half_frame()
        period = 37282 if self.mode5 else 29830
        if self.clock >= period:
            self.clock -= period
            if not self.mode5 and not self.inhibit: self.frame_irq = True

    def read_status(self):
        out = sum((1 << i) for i, length in enumerate(self.lengths) if length)
        if self.frame_irq: out |= 64
        self.frame_irq = False
        return out

class PPU:
    """Scanline renderer with timed vblank, scrolling, sprites, and hit events.

    Raster writes take effect at line granularity. No fetch-level accuracy,
    secondary-OAM overflow bug, analog emphasis, or vblank suppression races.
    """
    def __init__(self, cart):
        self.cart = cart
        self.nt = bytearray(4096)
        self.palette = bytearray(32)
        self.oam = bytearray(256)
        self.ctrl = self.mask = self.status = self.oam_addr = 0
        self.v = self.t = self.fine_x = self.w = self.buffer = self.open_bus = 0
        self.scanline, self.dot, self.frame = 261, 0, 0
        self.next_event = 1
        self.nmi_line = False
        self.nmi_callback = None
        self.sprite_hit_dot = -1
        self.framebuffer = bytearray(WIDTH*HEIGHT)
        self.tile_cache = {}
        self.rgb_row_cache = {}
        self.palette_key = None
        self.bg_tables = ()
        self.sprite_key = None
        self.sprite_rows = [[] for _ in range(240)]
        self.limit_sprites = True

    @property
    def rendering(self):
        return bool(self.mask & 0x18)

    def nt_index(self, address):
        address = (address - 0x2000) & 0xfff
        page, offset = address >> 10, address & 1023
        if self.cart.mirroring == 'vertical': page &= 1
        elif self.cart.mirroring == 'horizontal': page >>= 1
        return page * 1024 + offset

    @staticmethod
    def palette_index(address):
        address &= 31
        if address in (0x10, 0x14, 0x18, 0x1c): address -= 16
        return address

    def read_mem(self, address):
        address &= 0x3fff
        if address < 0x2000: return self.cart.chr[address]
        if address < 0x3f00: return self.nt[self.nt_index(address)]
        return self.palette[self.palette_index(address)]

    def write_mem(self, address, value):
        address &= 0x3fff
        if address < 0x2000:
            if self.cart.chr_ram: self.cart.chr[address] = value
        elif address < 0x3f00: self.nt[self.nt_index(address)] = value
        else: self.palette[self.palette_index(address)] = value & 63

    def update_nmi(self):
        line = bool(self.status & 128 and self.ctrl & 128)
        if line and not self.nmi_line and self.nmi_callback: self.nmi_callback()
        self.nmi_line = line

    def increment_x(self):
        if self.v & 31 == 31:
            self.v = (self.v & ~31) ^ 0x400
        else: self.v += 1

    def increment_y(self):
        if self.v & 0x7000 != 0x7000: self.v += 0x1000
        else:
            self.v &= ~0x7000
            y = (self.v >> 5) & 31
            if y == 29:
                y = 0
                self.v ^= 0x800
            elif y == 31: y = 0
            else: y += 1
            self.v = (self.v & ~0x3e0) | y << 5

    def increment_data(self):
        if self.rendering and (self.scanline < 240 or self.scanline == 261):
            self.increment_x(); self.increment_y()
        else: self.v = (self.v + (32 if self.ctrl & 4 else 1)) & 0x7fff

    def read_register(self, reg):
        out = self.open_bus
        if reg == 2:
            out = (self.status & 0xe0) | (self.open_bus & 31)
            self.status &= ~128
            self.w = 0
            self.update_nmi()
        elif reg == 4: out = self.oam[self.oam_addr]
        elif reg == 7:
            address = self.v & 0x3fff
            value = self.read_mem(address)
            if address >= 0x3f00:
                out = (value & (0x30 if self.mask & 1 else 63)) | (self.open_bus & 0xc0)
                self.buffer = self.read_mem(address - 0x1000)
            else:
                out, self.buffer = self.buffer, value
            self.increment_data()
        self.open_bus = out
        return out

    def write_register(self, reg, value):
        self.open_bus = value
        if reg == 0:
            self.ctrl = value
            self.t = (self.t & ~0xc00) | (value & 3) << 10
            self.update_nmi()
        elif reg == 1: self.mask = value
        elif reg == 3: self.oam_addr = value
        elif reg == 4:
            self.oam[self.oam_addr] = value
            self.oam_addr = (self.oam_addr + 1) & 255
        elif reg == 5:
            if not self.w:
                self.t = (self.t & ~31) | (value >> 3)
                self.fine_x = value & 7
            else:
                self.t = (self.t & ~0x73e0) | (value & 7) << 12 | (value & 0xf8) << 2
            self.w ^= 1
        elif reg == 6:
            if not self.w: self.t = (self.t & 255) | (value & 63) << 8
            else:
                self.t = (self.t & 0x7f00) | value
                self.v = self.t
            self.w ^= 1
        elif reg == 7:
            self.write_mem(self.v, value)
            self.increment_data()

    def tile_row(self, address):
        lo, hi = self.cart.chr[address], self.cart.chr[address + 8]
        key = lo | hi << 8
        row = self.tile_cache.get(key)
        if row is None:
            row = bytes(((lo >> bit) & 1) | (((hi >> bit) & 1) << 1) for bit in range(7, -1, -1))
            self.tile_cache[key] = row
        return row

    def render_line(self, line):
        backdrop = self.palette[0]
        colors = bytearray([backdrop]) * 256
        opaque = bytearray(256)
        if self.mask & 8:
            v, fine_y = self.v, (self.v >> 12) & 7
            base = 0x1000 if self.ctrl & 16 else 0
            key = bytes(self.palette[:16])
            if key != self.palette_key:
                self.palette_key = key
                self.bg_tables = tuple(bytes((backdrop, key[i+1], key[i+2], key[i+3])) + bytes(252)
                                       for i in (0,4,8,12))
            offsets = {'vertical': (0,1024,0,1024), 'horizontal': (0,0,1024,1024),
                       'four-screen': (0,1024,2048,3072)}[self.cart.mirroring]
            x = -self.fine_x
            while x < 256:
                nt_base = offsets[(v >> 10) & 3]
                tile = self.nt[nt_base + (v & 0x3ff)]
                attribute = self.nt[nt_base + 0x3c0 + ((v >> 4) & 0x38) + ((v >> 2) & 7)]
                shift = ((v >> 4) & 4) | (v & 2)
                row = self.tile_row(base + tile*16 + fine_y)
                if row != b'\0'*8:
                    palette_table = self.bg_tables[(attribute >> shift) & 3]
                    if 0 <= x <= 248:
                        colors[x:x+8] = row.translate(palette_table)
                        opaque[x:x+8] = row.translate(OPAQUE_TABLE)
                    else:
                        left, right = max(x,0), min(x+8,256)
                        cropped = row[left-x:right-x]
                        colors[left:right] = cropped.translate(palette_table)
                        opaque[left:right] = cropped.translate(OPAQUE_TABLE)
                if v & 31 == 31: v = (v & ~31) ^ 0x400
                else: v += 1
                x += 8
            if not self.mask & 2:
                colors[:8] = bytes([backdrop])*8
                opaque[:8] = b'\0'*8
        self.sprite_hit_dot = -1
        if self.mask & 16:
            height = 16 if self.ctrl & 32 else 8
            key = (bytes(self.oam), height)
            if key != self.sprite_key:
                self.sprite_key = key
                self.sprite_rows = [[] for _ in range(240)]
                for index in range(64):
                    y = self.oam[index*4] + 1
                    for sy in range(y, min(y+height,240)):
                        self.sprite_rows[sy].append((index, sy-y))
            sprites = self.sprite_rows[line]
            if len(sprites) > 8: self.status |= 32
            if self.limit_sprites: sprites = sprites[:8]
            occupied = bytearray(256)
            for index, row_num in sprites:
                _, tile, attr, x = self.oam[index*4:index*4+4]
                if attr & 128: row_num = height-1-row_num
                if height == 16:
                    address = (tile & 1)*0x1000 + (tile & 0xfe)*16 + (row_num//8)*16 + (row_num & 7)
                else: address = (0x1000 if self.ctrl & 8 else 0) + tile*16 + row_num
                row = self.tile_row(address)
                if attr & 64: row = row[::-1]
                for i in range(min(8, 256-x)):
                    px, val = x+i, row[i]
                    if not val or (px < 8 and not self.mask & 4): continue
                    if index == 0 and opaque[px] and px < 255 and self.sprite_hit_dot < 0:
                        self.sprite_hit_dot = px + 1
                    if occupied[px]: continue
                    occupied[px] = 1
                    if not (attr & 32 and opaque[px]):
                        colors[px] = self.palette[16 + (attr & 3)*4 + val]
        if not self.rendering and self.v & 0x3fff >= 0x3f00:
            colors[:] = bytes([self.read_mem(self.v)]) * 256
        if self.mask & 1:
            colors = colors.translate(GRAYSCALE_TABLE)
        self.framebuffer[line*256:(line+1)*256] = colors

    def tick(self, cycles):
        # The overwhelmingly common case stays inside the current scanline.
        # Keep the next event cached so every CPU instruction avoids a search.
        while cycles:
            remaining = self.next_event - self.dot
            if cycles < remaining:
                self.dot += cycles
                return
            self.dot = self.next_event
            cycles -= remaining
            line, dot = self.scanline, self.dot
            if line < 240:
                if dot == 1: self.render_line(line)
                if dot == self.sprite_hit_dot: self.status |= 64
                if self.rendering:
                    if dot == 256: self.increment_y()
                    elif dot == 257: self.v = (self.v & ~0x41f) | (self.t & 0x41f)
            elif line == 241 and dot == 1:
                self.status |= 128
                self.update_nmi()
            elif line == 261:
                if dot == 1:
                    self.status &= ~0xe0
                    self.update_nmi()
                elif self.rendering:
                    if dot == 257: self.v = (self.v & ~0x41f) | (self.t & 0x41f)
                    elif dot in (280, 304): self.v = (self.v & ~0x7be0) | (self.t & 0x7be0)
            if dot == 341:
                self.dot = 0
                self.scanline = (line + 1) % 262
                if self.scanline == 0: self.frame += 1
                self.next_event = 1 if self.scanline < 240 or self.scanline in (241,261) else 341
            elif line < 240:
                self.next_event = 256 if dot < 256 else 257 if dot == 256 else 341
                if dot < self.sprite_hit_dot < self.next_event:
                    self.next_event = self.sprite_hit_dot
            elif line == 261:
                self.next_event = 257 if dot < 257 else 280 if dot < 280 else 304 if dot < 304 else 341
            else:
                self.next_event = 341

    def rgb(self):
        return b''.join(map(PALETTE.__getitem__, self.framebuffer))

    def rgb_scaled(self):
        # Exact 5/4 nearest-neighbor scale. Identical scanlines reuse RGB bytes.
        rows = []
        doubled = tuple(color*2 for color in PALETTE)
        cache = self.rgb_row_cache
        for y in range(240):
            source = bytes(self.framebuffer[y*256:(y+1)*256])
            row = cache.get(source)
            if row is None:
                row = b''.join(doubled[c] if x%4 == 0 else PALETTE[c]
                               for x,c in enumerate(source))
                cache[source] = row
            rows.append(row)
            if y%4 == 0: rows.append(row)
        if len(cache) > 1024: cache.clear()
        return b''.join(rows)

class Bus:
    def __init__(self, cart, ppu, apu):
        self.cart, self.ppu, self.apu = cart, ppu, apu
        self.prg = cart.prg if len(cart.prg) == 32768 else cart.prg*2
        self.ram = bytearray(2048)
        self.controllers = [Controller(), Controller()]
        self.open_bus = 0
        self.dma_page = None

    @property
    def irq(self): return self.apu.frame_irq

    def read(self, address):
        address &= 0xffff
        if address >= 0x8000: value = self.prg[address & 0x7fff]
        elif address < 0x2000: value = self.ram[address & 0x7ff]
        elif address < 0x4000: value = self.ppu.read_register(address & 7)
        elif address == 0x4015: value = self.apu.read_status()
        elif address in (0x4016, 0x4017): value = (self.open_bus & 0xe0) | 0x40 | self.controllers[address & 1].read()
        elif address >= 0x6000: value = self.cart.ram[address & 0x1fff]
        else: value = self.open_bus
        self.open_bus = value
        return value

    def write(self, address, value):
        address &= 0xffff
        value &= 255
        self.open_bus = value
        if address < 0x2000: self.ram[address & 0x7ff] = value
        elif address < 0x4000: self.ppu.write_register(address & 7, value)
        elif address == 0x4014: self.dma_page = value
        elif address == 0x4016:
            for controller in self.controllers: controller.write(value)
        elif 0x4000 <= address <= 0x4017: self.apu.write(address, value)
        elif address >= 0x6000: self.cart.write(address, value)

class NES:
    def __init__(self, data, name='Cartridge'):
        self.source = bytes(data)
        self.cart = Cartridge(self.source, name)
        self.ppu = PPU(self.cart)
        self.apu = SilentAPU()
        self.bus = Bus(self.cart, self.ppu, self.apu)
        self.cpu = CPU(self.bus)
        self.ppu.nmi_callback = self.signal_nmi
        self.cpu.reset()
        self.ppu.tick(21)
        self.apu.tick(7)
        self.instructions = 0

    def signal_nmi(self): self.cpu.nmi_pending = True

    def step(self):
        cycles = self.cpu.step()
        self.instructions += 1
        self.ppu.tick(cycles * 3)
        self.apu.tick(cycles)
        if self.bus.dma_page is not None:
            page = self.bus.dma_page << 8
            self.bus.dma_page = None
            stall = 513 + (self.cpu.cycles & 1)
            start = self.ppu.oam_addr
            for i in range(256): self.ppu.oam[(start+i) & 255] = self.bus.read(page+i)
            self.cpu.cycles += stall
            self.ppu.tick(stall*3)
            self.apu.tick(stall)
            cycles += stall
        return cycles

    def frame(self):
        target = self.ppu.frame + 1
        while self.ppu.frame < target: self.step()

    def reset(self):
        limit = self.ppu.limit_sprites
        self.__init__(self.source, self.cart.name)
        self.ppu.limit_sprites = limit

class Assembler:
    """Tiny private assembler used only to generate our original demo ROM."""
    def __init__(self, base=0x8000):
        self.base, self.data, self.labels, self.fixups = base, bytearray(), {}, []

    def label(self, name): self.labels[name] = self.base + len(self.data)
    def emit(self, *values): self.data.extend(values)
    def word(self, opcode, value): self.emit(opcode, value & 255, value >> 8)
    def ref(self, opcode, name, offset=0):
        self.emit(opcode, 0, 0)
        self.fixups.append((len(self.data)-2, name, offset, False))
    def branch(self, opcode, name):
        self.emit(opcode, 0)
        self.fixups.append((len(self.data)-1, name, 0, True))
    def finish(self):
        for at, name, offset, relative in self.fixups:
            address = self.labels[name] + offset
            if relative:
                diff = address - (self.base+at+1)
                if not -128 <= diff <= 127: raise ValueError('Demo branch too long')
                self.data[at] = diff & 255
            else:
                self.data[at:at+2] = bytes((address & 255, address >> 8))
        return self.data

# Original 5x7 glyphs, represented as hand-written rows. No external game assets.
FONT = {
'A': ('01110','10001','10001','11111','10001','10001','10001'),
'B': ('11110','10001','10001','11110','10001','10001','11110'),
'C': ('01111','10000','10000','10000','10000','10000','01111'),
'D': ('11110','10001','10001','10001','10001','10001','11110'),
'E': ('11111','10000','10000','11110','10000','10000','11111'),
'F': ('11111','10000','10000','11110','10000','10000','10000'),
'G': ('01111','10000','10000','10111','10001','10001','01111'),
'H': ('10001','10001','10001','11111','10001','10001','10001'),
'I': ('11111','00100','00100','00100','00100','00100','11111'),
'J': ('00111','00010','00010','00010','10010','10010','01100'),
'K': ('10001','10010','10100','11000','10100','10010','10001'),
'L': ('10000','10000','10000','10000','10000','10000','11111'),
'M': ('10001','11011','10101','10101','10001','10001','10001'),
'N': ('10001','11001','11001','10101','10011','10011','10001'),
'O': ('01110','10001','10001','10001','10001','10001','01110'),
'P': ('11110','10001','10001','11110','10000','10000','10000'),
'Q': ('01110','10001','10001','10001','10101','10010','01101'),
'R': ('11110','10001','10001','11110','10100','10010','10001'),
'S': ('01111','10000','10000','01110','00001','00001','11110'),
'T': ('11111','00100','00100','00100','00100','00100','00100'),
'U': ('10001','10001','10001','10001','10001','10001','01110'),
'V': ('10001','10001','10001','10001','10001','01010','00100'),
'W': ('10001','10001','10001','10101','10101','10101','01010'),
'X': ('10001','10001','01010','00100','01010','10001','10001'),
'Y': ('10001','10001','01010','00100','00100','00100','00100'),
'Z': ('11111','00001','00010','00100','01000','10000','11111'),
'0': ('01110','10001','10011','10101','11001','10001','01110'),
'1': ('00100','01100','00100','00100','00100','00100','01110'),
'2': ('01110','10001','00001','00010','00100','01000','11111'),
':': ('00000','00100','00100','00000','00100','00100','00000'),
'/': ('00001','00001','00010','00100','01000','10000','10000'),
'-': ('00000','00000','00000','11111','00000','00000','00000'),
}

def demo_rom():
    """Assemble a genuine NROM program using the same CPU/PPU as loaded ROMs."""
    a = Assembler()
    a.label('reset')
    a.emit(0x78, 0xd8, 0xa2, 0xff, 0x9a, 0xa9, 0)
    for addr in (0x2000, 0x2001, 0x4010): a.word(0x8d, addr)
    a.emit(0xa9, 0x40); a.word(0x8d, 0x4017)
    a.emit(0xa2, 0, 0xa9, 0)
    a.label('clear')
    for addr in (0x0000, 0x0100, 0x0300, 0x0400, 0x0500, 0x0600, 0x0700): a.word(0x9d, addr)
    a.emit(0xe8); a.branch(0xd0, 'clear')
    a.emit(0xa9, 0xff)
    a.label('oamclear'); a.word(0x9d, 0x0200); a.emit(0xe8); a.branch(0xd0, 'oamclear')
    for label in ('vblank1', 'vblank2'):
        a.label(label); a.word(0x2c, 0x2002); a.branch(0x10, label)
    a.emit(0xa9, 0x3f); a.word(0x8d, 0x2006)
    a.emit(0xa9, 0); a.word(0x8d, 0x2006)
    a.emit(0xa2, 0)
    a.label('palette_loop'); a.ref(0xbd, 'palette'); a.word(0x8d, 0x2007)
    a.emit(0xe8, 0xe0, 32); a.branch(0xd0, 'palette_loop')
    a.emit(0xa9, 0x20); a.word(0x8d, 0x2006)
    a.emit(0xa9, 0); a.word(0x8d, 0x2006)
    a.emit(0xa2, 0)
    for page in range(4):
        a.label(f'nt{page}'); a.ref(0xbd, 'nametable', page*256); a.word(0x8d, 0x2007)
        a.emit(0xe8); a.branch(0xd0, f'nt{page}')
    a.emit(0xa9, 120, 0x85, 3, 0xa9, 105, 0x85, 4, 0xa9, 0x21, 0x85, 5)
    a.emit(0xa9, 0); a.word(0x8d, 0x2005); a.word(0x8d, 0x2005)
    a.emit(0xa9, 0x80); a.word(0x8d, 0x2000)
    a.emit(0xa9, 0x1e); a.word(0x8d, 0x2001)
    a.label('main'); a.emit(0xa5, 0, 0xc5, 1); a.branch(0xf0, 'main'); a.emit(0x85, 1)
    a.emit(0xa9, 1); a.word(0x8d, 0x4016)
    a.emit(0xa9, 0); a.word(0x8d, 0x4016); a.emit(0x85, 2, 0xa2, 8)
    a.label('readpad'); a.word(0xad, 0x4016); a.emit(0x4a, 0x26, 2, 0xca); a.branch(0xd0, 'readpad')
    for name, mask, zp, limit, increment in (
        ('right', 1, 3, 239, True), ('left', 2, 3, 1, False),
        ('down', 4, 4, 222, True), ('up', 8, 4, 1, False)):
        a.emit(0xa5, 2, 0x29, mask); a.branch(0xf0, 'skip_'+name)
        a.emit(0xa5, zp, 0xc9, limit); a.branch(0xb0 if increment else 0x90, 'skip_'+name)
        a.emit(0xe6 if increment else 0xc6, zp)
        a.label('skip_'+name)
    a.emit(0xa5, 2, 0x29, 0x10); a.branch(0xf0, 'notstart')
    a.emit(0xa9, 120, 0x85, 3, 0xa9, 105, 0x85, 4)
    a.label('notstart')
    a.emit(0xa9, 0x21, 0x85, 5, 0xa5, 2, 0x29, 0x80); a.branch(0xf0, 'nota')
    a.emit(0xa9, 0x29, 0x85, 5)
    a.label('nota'); a.emit(0xa5, 2, 0x29, 0x40); a.branch(0xf0, 'notb')
    a.emit(0xa9, 0x16, 0x85, 5)
    a.label('notb')
    for i in range(4):
        a.emit(0xa5, 4)
        if i >= 2: a.emit(0x18, 0x69, 8)
        a.word(0x8d, 0x200+i*4)
        a.emit(0xa9, 128+i); a.word(0x8d, 0x201+i*4)
        a.emit(0xa9, 0); a.word(0x8d, 0x202+i*4)
        a.emit(0xa5, 3)
        if i & 1: a.emit(0x18, 0x69, 8)
        a.word(0x8d, 0x203+i*4)
    a.ref(0x4c, 'main')
    a.label('nmi'); a.emit(0x48, 0x8a, 0x48, 0x98, 0x48)
    a.emit(0xa9, 0); a.word(0x8d, 0x2003)
    a.emit(0xa9, 2); a.word(0x8d, 0x4014)
    a.emit(0xa9, 0x3f); a.word(0x8d, 0x2006)
    a.emit(0xa9, 0x11); a.word(0x8d, 0x2006)
    a.emit(0xa5, 5); a.word(0x8d, 0x2007)
    a.emit(0xa9, 0); a.word(0x8d, 0x2005); a.word(0x8d, 0x2005)
    a.emit(0xa9, 0x80); a.word(0x8d, 0x2000)
    a.emit(0xe6, 0, 0x68, 0xa8, 0x68, 0xaa, 0x68)
    a.label('irq'); a.emit(0x40)
    a.label('palette')
    a.data.extend(bytes([0x0f,0x21,0x30,0x12]*4+[0x0f,0x21,0x30,0x12]*4))
    a.label('nametable')
    nt = bytearray(1024)
    for x in range(2,30): nt[2*32+x] = nt[27*32+x] = 127
    for y in range(2,28): nt[y*32+2] = nt[y*32+29] = 127
    for row, text in ((5,'BLUE NES'),(7,'ORIGINAL NROM DEMO'),(20,'ARROWS : MOVE'),(22,'Z / X : COLOR'),(24,'ENTER : CENTER')):
        col = (32-len(text))//2
        for i, ch in enumerate(text): nt[row*32+col+i] = ord(ch) if ch != ' ' else 0
    a.data.extend(nt)
    code = a.finish()
    prg = bytearray([0xea])*16384
    prg[:len(code)] = code
    for offset, label in ((0x3ffa,'nmi'),(0x3ffc,'reset'),(0x3ffe,'irq')):
        address = a.labels[label]; prg[offset:offset+2] = bytes((address&255,address>>8))
    chr_data = bytearray(8192)
    for ch, rows in FONT.items():
        for y, row in enumerate(rows): chr_data[ord(ch)*16+y] = int(row,2) << 2
    chr_data[127*16:127*16+8] = b'\xff'*8
    # Four original quadrant tiles make a bordered 16x16 controller chip.
    for tile in range(4):
        for y in range(8):
            for x in range(8):
                gx, gy = x+(tile&1)*8, y+(tile//2)*8
                value = 2 if gx in (0,15) or gy in (0,15) else 1
                if (gx in (4,5) and 4 <= gy <= 11) or (gy in (7,8) and 2 <= gx <= 7): value = 3
                if (gx,gy) in ((11,6),(12,6),(11,7),(12,7),(10,10),(11,10)): value = 2
                index = (128+tile)*16+y
                chr_data[index] |= (value&1) << (7-x)
                chr_data[index+8] |= (value>>1) << (7-x)
    return b'NES\x1a'+bytes((1,1,1,0,0,0,0,0,0,0,0,0))+prg+chr_data

HELP_TEXT = '''BLUE NES 0.1\nSingle-file, silent NTSC NROM emulator\n\nOpen ROM loads an extracted .nes file. Only iNES mapper 0 (NROM) is supported: 16/32 KiB PRG, 8 KiB CHR-ROM or CHR-RAM. Other mappers, PAL, NES 2.0 and disk systems are rejected.\n\nPlayer 1\nArrows = D-pad    Z = A    X = B\nEnter = Start    Right Shift = Select\n\nPlayer 2\nI/J/K/L = Up/Left/Down/Right\nG = A    H = B    T = Start    Y = Select\n\nShortcuts\nSpace = Play / Pause    Escape = Pause\nCtrl+O = Open ROM    F2 = Original demo\nF5 = Reset    F6 = One frame    F1 = Help\n\nClick the game area if your keyboard is focused elsewhere. Focus loss releases every key; automatic pause is enabled by default. Settings and Help pause emulation while open.\n\nThe demo runs genuine 6502 code through this emulator. Move the chip with the arrows, hold Z or X to change its color, and press Enter to center it.\n\nLIMITATIONS\nNo audio synthesis or DMC. APU frame IRQ/length status are approximate. PPU rendering is scanline-based; mid-line effects, precise interrupt/DMA bus timing, odd-frame dot skip, sprite-overflow hardware bug and color emphasis are not implemented. Unstable unofficial CPU opcodes stop with an error. Some NROM games will be imperfect or fail. Speed depends on your CPU and can be below 60 FPS.\n\nNo settings, save RAM or save states are written to disk. Reset is a fresh power cycle and clears volatile cartridge RAM. Closing the app loses all progress. Only use ROMs you have a right to use. No commercial game is included.'''

class App:
    BG = '#040b16'
    PANEL = '#081a30'
    BLUE = '#2999ff'
    TEXT = '#e4f1ff'
    MUTED = '#7e9ab8'
    NES_W, NES_H = 256, 240
    SIDE_W = 320
    HEADER_H = 52
    TOOLBAR_Y = 58
    TOOLBAR_H = 36
    PAD = 20
    STATUS_H = 30
    KEYMAP = {'z': (0,0), 'x': (0,1), 'Shift_R': (0,2), 'Return': (0,3),
              'Up': (0,4), 'Down': (0,5), 'Left': (0,6), 'Right': (0,7),
              'g': (1,0), 'h': (1,1), 'y': (1,2), 't': (1,3),
              'i': (1,4), 'k': (1,5), 'j': (1,6), 'l': (1,7)}

    def __init__(self, root):
        import tkinter as tk
        self.tk, self.root = tk, root
        self.nes = None
        self.running = self.closed = False
        self.modal = None
        self.timer = None
        self.release_jobs = {}
        self.pressed = set()
        self.speed = 1.0
        self.auto_pause = True
        self.sprite_limit = True
        self.frames_presented = 0
        self.fps = 0.0
        self.measure_start = time.perf_counter()
        self.target_time = 0.0
        self.frame_target = None
        self.step_once = False
        self.last_error = ''
        root.withdraw()
        root.title(f'Blue NES {VERSION} | NROM')
        root.resizable(False, False)
        root.configure(bg=self.BG)
        root.protocol('WM_DELETE_WINDOW', self.close)
        root.option_add('*Font', ('Arial',11))
        self._layout_from_screen()
        self.status = tk.StringVar(value='Ready | no ROM loaded')
        self.title_text = tk.StringVar(value='LOAD A CARTRIDGE')
        self.detail_text = tk.StringVar(value='NROM · NTSC\n\nOriginal demo included\nNo game downloads needed')
        self.stats_text = tk.StringVar(value='SILENT BUILD\nCPU 2A03  /  PPU 2C02')
        self.make_header()
        self.make_toolbar()
        view_top = self.HEADER_H + self.TOOLBAR_H + 12
        cw, ch = self.VIEW_W + 2, self.VIEW_H + 2
        self.canvas = tk.Canvas(root, width=self.VIEW_W, height=self.VIEW_H, bg='#000000',
                                highlightthickness=1, highlightbackground='#163755')
        self.canvas.place(x=self.PAD, y=view_top, width=cw, height=ch)
        self.canvas.bind('<Button-1>', lambda e: self.canvas.focus_set())
        self.screen_item = self.canvas.create_image(self.VIEW_W // 2, self.VIEW_H // 2)
        self.splash_items = []
        self.draw_splash()
        side_x = self.PAD + cw + 16
        side = tk.Frame(root, bg=self.PANEL)
        side.place(x=side_x, y=view_top, width=self.SIDE_W, height=ch)
        inner = self.SIDE_W - 32
        tk.Label(side, textvariable=self.title_text, fg=self.TEXT, bg=self.PANEL, font=('Arial', 15, 'bold'),
                 wraplength=inner, justify='left', anchor='w').place(x=16, y=20, width=inner, height=56)
        tk.Label(side, textvariable=self.detail_text, fg=self.MUTED, bg=self.PANEL, justify='left',
                 anchor='nw', font=('Arial', 12)).place(x=16, y=88, width=inner, height=100)
        tk.Frame(side, bg='#183958', height=1).place(x=16, y=200, width=inner)
        tk.Label(side, text='PLAYER 1', fg=self.BLUE, bg=self.PANEL, font=('Arial', 12, 'bold'),
                 anchor='w').place(x=16, y=220)
        tk.Label(side, text='Arrows     D-pad\nZ / X         A / B\nEnter        Start\nR Shift      Select',
                 fg=self.TEXT, bg=self.PANEL, justify='left', font=('Arial', 13)).place(x=16, y=252)
        tk.Label(side, textvariable=self.stats_text, fg=self.MUTED, bg=self.PANEL, justify='left',
                 font=('Arial', 12), anchor='nw').place(x=16, y=ch - 90, width=inner, height=70)
        status_y = view_top + ch + 10
        tk.Label(root, textvariable=self.status, bg=self.BG, fg=self.MUTED, font=('Arial', 11),
                 anchor='w').place(x=self.PAD, y=status_y, width=self.WIN_W - self.PAD * 2, height=22)
        root.bind('<KeyPress>', self.key_down)
        root.bind('<KeyRelease>', self.key_up)
        root.bind('<FocusOut>', lambda e: root.after_idle(self.focus_lost))
        root.bind('<Control-o>', lambda e: self.open_rom())
        root.bind('<Control-O>', lambda e: self.open_rom())
        root.bind('<F1>', lambda e: self.help())
        root.bind('<F2>', lambda e: self.load_demo())
        root.bind('<F5>', lambda e: self.reset())
        root.bind('<F6>', lambda e: self.single_frame())
        self.refresh_buttons()
        root.minsize(self.WIN_W, self.WIN_H)
        root.maxsize(self.WIN_W, self.WIN_H)
        self.center_window(root, self.WIN_W, self.WIN_H)
        root.deiconify()
        root.lift()
        root.focus_force()
        # macOS adjusts chrome on map; re-assert size and center.
        root.after_idle(self._recenter)
        root.after(100, self._recenter)

    def _layout_from_screen(self):
        """Choose a large, centered integer-scaled NES window that fits the desktop."""
        self.root.update_idletasks()
        sw = max(self.root.winfo_screenwidth(), 800)
        sh = max(self.root.winfo_screenheight(), 600)

        # Leave room for the desktop menu bar / dock and window decorations.
        usable_w = max(760, sw - 80)
        usable_h = max(600, sh - 120)
        chrome_h = self.HEADER_H + self.TOOLBAR_H + self.STATUS_H + 36
        chrome_w = self.SIDE_W + self.PAD * 2 + 24

        zoom_w = max(1, (usable_w - chrome_w) // self.NES_W)
        zoom_h = max(1, (usable_h - chrome_h) // self.NES_H)
        self.zoom = max(2, min(zoom_w, zoom_h, 4))

        self.VIEW_W = self.NES_W * self.zoom
        self.VIEW_H = self.NES_H * self.zoom
        self.WIN_W = self.PAD + self.VIEW_W + 2 + 16 + self.SIDE_W + self.PAD
        self.WIN_H = self.HEADER_H + self.TOOLBAR_H + 12 + self.VIEW_H + 2 + 10 + self.STATUS_H

    def _recenter(self):
        if not self.closed:
            self.center_window(self.root, self.WIN_W, self.WIN_H)

    def center_window(self, window, width, height, parent=None):
        window.update_idletasks()
        if parent is not None:
            px = parent.winfo_rootx()
            py = parent.winfo_rooty()
            pw = max(parent.winfo_width(), width)
            ph = max(parent.winfo_height(), height)
            x = px + (pw - width) // 2
            y = py + (ph - height) // 2
        else:
            sw = window.winfo_screenwidth()
            sh = window.winfo_screenheight()
            x = max(0, (sw - width) // 2)
            y = max(0, (sh - height) // 2)
        window.geometry(f'{width}x{height}+{x}+{y}')
        window.update_idletasks()

    def button(self, parent, text, command, **kwargs):
        return self.tk.Button(parent,text=text,command=command,bg='#102a47',fg=self.TEXT,activebackground='#184c7c',activeforeground='#ffffff',disabledforeground='#42566e',relief='flat',borderwidth=0,highlightthickness=0,padx=8,pady=4,takefocus=False,**kwargs)

    def make_header(self):
        tk=self.tk
        tk.Frame(self.root,bg='#07315a').place(x=0,y=0,width=self.WIN_W,height=self.HEADER_H)
        tk.Label(self.root,text='BLUE NES',fg='#ffffff',bg='#07315a',font=('Arial',22,'bold')).place(x=18,y=8)
        tk.Label(self.root,text='NROM / 0.1',fg='#8dcaff',bg='#07315a',font=('Arial',12,'bold')).place(x=196,y=18)
        size_label = f'{self.WIN_W}×{self.WIN_H}  |  {self.zoom}×  |  TKINTER'
        tk.Label(self.root,text=size_label,fg='#8dcaff',bg='#07315a',font=('Arial',11)).place(
            x=self.WIN_W - 18, y=18, anchor='ne')

    def make_toolbar(self):
        commands = [('Open ROM',self.open_rom,self.PAD,120),('Demo',self.load_demo,self.PAD+132,76),
                    ('Play',self.toggle,self.PAD+218,84),('Reset',self.reset,self.PAD+312,76),
                    ('Step',self.single_frame,self.PAD+398,70),
                    ('Settings',self.settings,self.WIN_W-230,108),('Help',self.help,self.WIN_W-112,90)]
        self.buttons = {}
        for name,command,x,width in commands:
            b=self.button(self.root,name,command)
            b.place(x=x,y=self.TOOLBAR_Y,width=width,height=self.TOOLBAR_H-4)
            self.buttons[name]=b

    def draw_splash(self):
        for item in self.splash_items: self.canvas.delete(item)
        cx, cy = self.VIEW_W // 2, self.VIEW_H // 2
        s = max(1, self.zoom)
        self.splash_items = [
            self.canvas.create_rectangle(cx-48*s, cy-71*s, cx+48*s, cy-18*s, outline=self.BLUE, width=max(2, s)),
            self.canvas.create_rectangle(cx-29*s, cy-80*s, cx+29*s, cy-68*s, fill='#0d416d', outline=self.BLUE),
            self.canvas.create_text(cx, cy-44*s, text='NES', fill=self.BLUE, font=('Arial', 18*s, 'bold')),
            self.canvas.create_text(cx, cy+20*s, text='YOUR ROM. YOUR MACHINE.', fill=self.TEXT, font=('Arial', 7*s, 'bold')),
            self.canvas.create_text(cx, cy+45*s, text='Open a mapper 0 .nes cartridge\nor try the original built-in demo',
                                    fill=self.MUTED, font=('Arial', 6*s), justify='center'),
            self.canvas.create_text(cx, cy+90*s, text='NO AUDIO  |  EARLY COMPATIBILITY BUILD', fill='#426c95', font=('Arial', 5*s))]

    def refresh_buttons(self):
        have = self.nes is not None
        self.buttons['Play'].configure(text='Pause' if self.running else 'Play',state='normal' if have else 'disabled')
        self.buttons['Reset'].configure(state='normal' if have else 'disabled')
        self.buttons['Step'].configure(state='normal' if have and not self.running else 'disabled')

    def pause(self, reason=None):
        self.running = self.step_once = False
        self.frame_target = None
        if self.timer is not None:
            self.root.after_cancel(self.timer)
            self.timer = None
        self.release_all()
        self.refresh_buttons()
        if self.nes: self.status.set(reason or 'Paused | Space to play / F6 to step')

    def play(self):
        if not self.nes or self.modal or self.closed: return
        if self.nes.cpu.halted:
            self.show_error('Reset needed', 'The CPU stopped on an unsupported instruction. Press Reset or load another ROM.')
            return
        self.running = True
        self.step_once = False
        self.target_time = time.perf_counter()
        self.frame_target = None
        self.measure_start = self.target_time
        self.frames_presented = 0
        self.refresh_buttons()
        if self.timer is None: self.timer = self.root.after(0,self.tick)

    def toggle(self):
        if self.modal: return
        if self.running: self.pause()
        else: self.play()

    def single_frame(self):
        if not self.nes or self.modal or self.running or self.nes.cpu.halted: return
        self.pause()
        self.step_once = True
        self.frame_target = self.nes.ppu.frame+1
        self.timer = self.root.after(0,self.tick)

    def tick(self):
        self.timer = None
        if self.closed or not self.nes or not (self.running or self.step_once): return
        now = time.perf_counter()
        if self.running and self.frame_target is None and now < self.target_time:
            self.timer = self.root.after(max(1,int((self.target_time-now)*1000)),self.tick)
            return
        if self.frame_target is None: self.frame_target = self.nes.ppu.frame+1
        end = now+0.007
        try:
            while self.nes.ppu.frame < self.frame_target and time.perf_counter() < end:
                self.nes.step()
        except (CPUError, ValueError, IndexError) as exc:
            self.pause('Stopped | reset or load another ROM')
            self.show_error('Emulation stopped',str(exc))
            return
        if self.nes.ppu.frame >= self.frame_target:
            self.frame_target = None
            self.present()
            self.frames_presented += 1
            elapsed=time.perf_counter()-self.measure_start
            if elapsed >= 0.5:
                self.fps=self.frames_presented/elapsed
                self.frames_presented=0; self.measure_start=time.perf_counter()
            if self.step_once:
                self.step_once=False
                self.status.set(f'Paused | frame {self.nes.ppu.frame:,} | F6 to step again')
                return
            self.target_time += 1/(60.0988*self.speed)
            if time.perf_counter()-self.target_time > 0.1: self.target_time=time.perf_counter()
            self.status.set(f'Playing | {self.fps:4.1f} FPS | {self.speed:g}x target | no audio')
        # Yield to pending input/redraw without paying a coarse OS timer tick.
        self.timer = self.root.after_idle(self.tick)

    def present(self):
        if not self.nes: return
        ppm=b'P6\n256 240\n255\n'+self.nes.ppu.rgb()
        image=self.tk.PhotoImage(data=ppm,format='PPM')
        if self.zoom > 1:
            image=image.zoom(self.zoom, self.zoom)
        self.image=image
        self.canvas.itemconfigure(self.screen_item,image=self.image)
        for item in self.splash_items: self.canvas.delete(item)
        self.splash_items=[]
        self.stats_text.set(f'Frame {self.nes.ppu.frame:,}  ·  PC ${self.nes.cpu.pc:04X}\nSILENT · scanline PPU')

    def load_bytes(self, data, name):
        candidate=NES(data,name)  # Validate before replacing the old cartridge.
        self.pause()
        self.nes=candidate
        candidate.ppu.limit_sprites=self.sprite_limit
        self.title_text.set(name if len(name)<=46 else name[:43]+'...')
        self.detail_text.set(f'NROM / mapper 0 · NTSC\n{len(candidate.cart.prg)//1024}K PRG · {"CHR-RAM" if candidate.cart.chr_ram else "8K CHR-ROM"}\n{candidate.cart.mirroring.title()} mirroring'+('\nBattery save is volatile' if candidate.cart.battery else ''))
        self.present()
        self.play()

    def open_rom(self):
        if self.modal: return
        from tkinter import filedialog
        was_running=self.running
        self.pause()
        self.modal=True
        try:
            path=filedialog.askopenfilename(parent=self.root,title='Open NTSC NROM cartridge',filetypes=[('NES ROM','*.nes'),('All files','*')])
        finally: self.modal=None
        if not path:
            if was_running: self.play()
            return
        try:
            with open(path,'rb') as stream: data=stream.read(Cartridge.MAX_SIZE+1)
            self.load_bytes(data,pathlib.Path(path).name)
        except (OSError,ROMError) as exc:
            self.show_error('Cannot load ROM',str(exc))
            if was_running: self.play()
        self.canvas.focus_set()

    def load_demo(self):
        if self.modal: return
        self.load_bytes(demo_rom(),'BLUE NES / original demo')
        self.canvas.focus_set()

    def reset(self):
        if not self.nes or self.modal: return
        was_running=self.running
        self.pause()
        self.nes.reset()
        self.present()
        self.status.set('Reset | volatile memory cleared')
        if was_running: self.play()

    def release_all(self):
        for job in self.release_jobs.values(): self.root.after_cancel(job)
        self.release_jobs.clear()
        self.pressed.clear()
        if self.nes:
            for pad in self.nes.bus.controllers: pad.buttons=0

    def key_down(self,event):
        if self.modal: return
        key=event.keysym
        if len(key)==1: key=key.lower()
        if key in self.release_jobs: self.root.after_cancel(self.release_jobs.pop(key))
        repeated = key in self.pressed
        if key in self.KEYMAP or key in ('space', 'Escape'): self.pressed.add(key)
        if key in ('space', 'Escape') and repeated: return 'break'
        if key=='space':
            self.toggle(); self.pressed.add(key); return 'break'
        if key=='Escape': self.pause(); return 'break'
        if self.nes and key in self.KEYMAP:
            player,button=self.KEYMAP[key]
            self.nes.bus.controllers[player].set(button,True)
            return 'break'

    def key_up(self,event):
        key=event.keysym
        if len(key)==1: key=key.lower()
        if key in self.KEYMAP or key in ('space', 'Escape'):
            if key in self.release_jobs: self.root.after_cancel(self.release_jobs.pop(key))
            self.release_jobs[key]=self.root.after_idle(lambda key=key:self.release_key(key))
            return 'break'

    def release_key(self,key):
        self.release_jobs.pop(key,None)
        self.pressed.discard(key)
        if self.nes and key in self.KEYMAP:
            player,button=self.KEYMAP[key]
            self.nes.bus.controllers[player].set(button,False)

    def focus_lost(self):
        if self.closed: return
        try: focused=self.root.focus_displayof()
        except (self.tk.TclError, KeyError): focused = None
        if focused is None:
            self.release_all()
            if self.auto_pause and self.running and not self.modal: self.pause('Paused | window lost focus')

    def dialog(self,title,width,height):
        if self.modal: return None
        resume=self.running
        self.pause()
        window=self.tk.Toplevel(self.root)
        self.modal=window
        window.title(title)
        window.configure(bg=self.PANEL); window.resizable(False,False)
        self.center_window(window, width, height, parent=self.root)
        window.transient(self.root); window.grab_set()
        def done():
            if self.closed: return
            window.grab_release(); window.destroy(); self.modal=None
            self.canvas.focus_set()
            if resume: self.play()
        window.protocol('WM_DELETE_WINDOW',done)
        window.bind('<Escape>',lambda e:done())
        return window,done

    def help(self):
        result=self.dialog('Blue NES | Help & limitations',540,470)
        if not result: return
        window,done=result
        frame=self.tk.Frame(window,bg=self.PANEL); frame.pack(fill='both',expand=True,padx=14,pady=12)
        scroll=self.tk.Scrollbar(frame); scroll.pack(side='right',fill='y')
        text=self.tk.Text(frame,wrap='word',bg=self.BG,fg=self.TEXT,insertbackground=self.TEXT,relief='flat',padx=12,pady=10,font=('Arial',10),yscrollcommand=scroll.set)
        text.pack(fill='both',expand=True); scroll.configure(command=text.yview)
        text.insert('1.0',HELP_TEXT); text.configure(state='disabled')
        self.button(window,'Close',done).pack(pady=(0,12))

    def settings(self):
        result=self.dialog('Blue NES | Session settings',390,320)
        if not result: return
        window,done=result
        tk=self.tk
        speed=tk.StringVar(value=f'{self.speed:g}x')
        pause=tk.BooleanVar(value=self.auto_pause)
        limit=tk.BooleanVar(value=self.sprite_limit)
        tk.Label(window,text='SESSION SETTINGS',fg=self.BLUE,bg=self.PANEL,font=('Arial',13,'bold')).pack(anchor='w',padx=22,pady=(20,12))
        row=tk.Frame(window,bg=self.PANEL); row.pack(fill='x',padx=22)
        tk.Label(row,text='Target speed',fg=self.TEXT,bg=self.PANEL).pack(side='left')
        choices=tk.OptionMenu(row,speed,'0.5x','1x','2x')
        choices.configure(bg='#102a47',fg=self.TEXT,highlightthickness=0,activebackground='#184c7c'); choices.pack(side='right')
        for label,var in [('Pause when window loses focus',pause),('NES 8 sprites per scanline limit',limit)]:
            tk.Checkbutton(window,text=label,variable=var,bg=self.PANEL,fg=self.TEXT,selectcolor=self.BG,activebackground=self.PANEL,activeforeground=self.TEXT).pack(anchor='w',padx=19,pady=8)
        tk.Label(window,text='No audio in this build.\nChanges last for this session only.\nHigher speeds depend on your computer.',justify='left',fg=self.MUTED,bg=self.PANEL,font=('Arial',9)).pack(anchor='w',padx=22,pady=10)
        def apply():
            self.speed=float(speed.get().rstrip('x'))
            self.auto_pause=pause.get(); self.sprite_limit=limit.get()
            if self.nes: self.nes.ppu.limit_sprites=self.sprite_limit
            done()
        controls=tk.Frame(window,bg=self.PANEL); controls.pack(fill='x',padx=22,pady=6)
        self.button(controls,'Apply',apply).pack(side='right')
        self.button(controls,'Cancel',done).pack(side='right',padx=8)

    def show_error(self,title,message):
        from tkinter import messagebox
        self.last_error=message
        previous=self.modal; self.modal=True
        try: messagebox.showerror(title,message,parent=self.root)
        finally: self.modal=previous

    def close(self):
        self.pause()
        self.closed=True
        self.root.destroy()

class CoreTests(unittest.TestCase):
    """Offline deterministic regression tests; no display or ROM files needed."""
    class FlatBus:
        def __init__(self): self.mem=bytearray(65536); self.irq=False
        def read(self,address): return self.mem[address & 0xffff]
        def write(self,address,value): self.mem[address & 0xffff]=value & 255

    def machine(self): return NES(demo_rom(),'Self-test')

    def cpu(self, program, pc=0x8000):
        bus=self.FlatBus(); bus.mem[pc:pc+len(program)]=bytes(program)
        bus.mem[0xfffc:0xfffe]=bytes((pc&255,pc>>8))
        cpu=CPU(bus); cpu.reset()
        return cpu,bus

    def test_adc_exhaustive(self):
        cpu,_=self.cpu([])
        for left in range(256):
            for right in range(256):
                for carry in (0,1):
                    cpu.a=left;cpu.p=U|D|carry;cpu.adc(right)
                    total=left+right+carry; value=total&255
                    expected=U|D|(C if total>255 else 0)|(Z if value==0 else 0)|(value&128)
                    if (~(left^right)&(left^value))&128: expected|=V
                    if (cpu.a,cpu.p)!=(value,expected): self.fail((left,right,carry,cpu.a,cpu.p,expected))

    def test_sbc_exhaustive(self):
        cpu,_=self.cpu([])
        for left in range(256):
            for right in range(256):
                for carry in (0,1):
                    cpu.a=left;cpu.p=U|D|carry;cpu.adc(right^255)
                    diff=left-right-(1-carry);value=diff&255
                    expected=U|D|(C if diff>=0 else 0)|(Z if value==0 else 0)|(value&128)
                    if ((left^right)&(left^value))&128: expected|=V
                    if (cpu.a,cpu.p)!=(value,expected): self.fail((left,right,carry,cpu.a,cpu.p,expected))

    def test_stack_and_subroutine(self):
        cpu,bus=self.cpu([0x20,0x10,0x80,0xea])
        bus.mem[0x8010:0x8014]=bytes([0xa9,0x77,0x48,0x68]);bus.mem[0x8014]=0x60
        self.assertEqual(cpu.step(),6);self.assertEqual(cpu.s,0xfb)
        self.assertEqual(bus.mem[0x1fd],0x80);self.assertEqual(bus.mem[0x1fc],2)
        for _ in range(4):cpu.step()
        self.assertEqual((cpu.pc,cpu.a,cpu.s),(0x8003,0x77,0xfd))

    def test_brk_rti(self):
        cpu,bus=self.cpu([0,0xea,0xea]);bus.mem[0xfffe:]=bytes([0,0x90]);bus.mem[0x9000]=0x40
        cpu.p=U|C
        self.assertEqual(cpu.step(),7)
        self.assertEqual(cpu.pc,0x9000);self.assertEqual(bus.mem[0x1fb],U|C|B)
        self.assertEqual(cpu.step(),6)
        self.assertEqual((cpu.pc,cpu.p,cpu.s),(0x8002,U|C,0xfd))

    def test_irq_cli_delay_and_nmi_priority(self):
        cpu,bus=self.cpu([0x58,0xea,0xea]);bus.mem[0xfffe:]=bytes([0,0x90]);bus.irq=True
        cpu.step();self.assertEqual(cpu.pc,0x8001)
        cpu.step();self.assertEqual(cpu.pc,0x8002)
        cpu.step();self.assertEqual(cpu.pc,0x9000)
        bus.mem[0xfffa:0xfffc]=bytes([0,0xa0]);cpu.nmi_pending=True
        cpu.step();self.assertEqual(cpu.pc,0xa000)
        self.assertFalse(bus.mem[0x1f8]&B)

    def test_indirect_jmp_bug(self):
        cpu,bus=self.cpu([0x6c,0xff,0x20]);bus.mem[0x20ff]=0x34;bus.mem[0x2000]=0x12;bus.mem[0x2100]=0xab
        cpu.step();self.assertEqual(cpu.pc,0x1234)

    def test_zero_page_index_and_pointer_wrap(self):
        cpu,bus=self.cpu([0xb5,0xff,0xb1,0xff]);cpu.x=2;cpu.y=1
        bus.mem[1]=0x42;bus.mem[0xff]=0xff;bus.mem[0]=0x30;bus.mem[0x3100]=0x79
        self.assertEqual(cpu.step(),4);self.assertEqual(cpu.a,0x42)
        self.assertEqual(cpu.step(),6);self.assertEqual(cpu.a,0x79)

    def test_page_cross_cycles_and_pc_wrap(self):
        cpu,bus=self.cpu([0xbd,0xff,0x20,0x9d,0xff,0x20]);cpu.x=1;bus.mem[0x2100]=123
        self.assertEqual(cpu.step(),5);self.assertEqual(cpu.a,123)
        self.assertEqual(cpu.step(),5)
        cpu.pc=0xfffe;bus.mem[0xfffe:]=bytes([0xa9,0x42]);cpu.step();self.assertEqual(cpu.pc,0)

    def test_branch_timing(self):
        cpu,bus=self.cpu([0xd0,0x7f],pc=0x80fd)
        self.assertEqual(cpu.step(),4);self.assertEqual(cpu.pc,0x817e)
        cpu.pc=0x80fd;cpu.p|=Z;self.assertEqual(cpu.step(),2);self.assertEqual(cpu.pc,0x80ff)

    def test_shift_rotate_and_flags(self):
        cpu,_=self.cpu([0x0a,0x6a,0x4a,0x2a]);cpu.a=0x81
        cpu.step();self.assertEqual((cpu.a,cpu.p&C),(2,1))
        cpu.step();self.assertEqual(cpu.a,0x81)
        cpu.step();self.assertEqual((cpu.a,cpu.p&C),(0x40,1))
        cpu.step();self.assertEqual(cpu.a,0x81)

    def test_stable_undocumented(self):
        cpu,bus=self.cpu([0x07,0x10,0x67,0x11,0xc7,0x12,0xe7,0x13,0xa7,0x14,0x87,0x15])
        cpu.a=1;bus.mem[0x10]=0x81;bus.mem[0x11]=2;bus.mem[0x12]=6;bus.mem[0x13]=1;bus.mem[0x14]=0x82
        cpu.step();self.assertEqual((cpu.a,bus.mem[0x10]),(3,2))
        cpu.step();self.assertEqual(cpu.a,0x84)
        cpu.step();self.assertEqual(bus.mem[0x12],5)
        cpu.step();self.assertEqual(bus.mem[0x13],2)
        cpu.step();self.assertEqual((cpu.a,cpu.x),(0x82,0x82))
        cpu.step();self.assertEqual(bus.mem[0x15],0x82)

    def test_jam_and_unstable_stop(self):
        for opcode in (2,0x8b,0x9f,0xab):
            cpu,_=self.cpu([opcode,0,0])
            with self.assertRaises(CPUError):cpu.step()
            self.assertTrue(cpu.halted)

    def test_nrom_mapping(self):
        n=self.machine()
        self.assertEqual(n.bus.read(0x8000),n.bus.read(0xc000))
        original=n.bus.read(0x8000);n.bus.write(0x8000,original^255)
        self.assertEqual(n.bus.read(0x8000),original)
        n.bus.write(0x6000,0x37);self.assertEqual(n.bus.read(0x6000),0x37)
        n.bus.write(0x17ff,0x92);self.assertEqual(n.bus.read(0x7ff),0x92)
        self.assertEqual(n.bus.read(0x1fff),0x92)

    def test_nrom_32k_and_trainer(self):
        data=bytearray(b'NES\x1a'+bytes([2,0,4]+[0]*9))
        data+=bytes([0x78])*512+bytes([0x12])*16384+bytes([0x34])*16384
        cart=Cartridge(data)
        self.assertEqual(cart.read(0x8000),0x12);self.assertEqual(cart.read(0xc000),0x34)
        self.assertEqual(cart.read(0x7000),0x78)
        self.assertTrue(cart.chr_ram)

    def test_rom_validation(self):
        good=demo_rom()
        for data in (b'',b'bad'*10,good[:100]):
            with self.assertRaises(ROMError):Cartridge(data)
        for offset,value in ((4,3),(5,2),(6,0x10),(7,8),(7,1),(9,1),(10,2)):
            bad=bytearray(good);bad[offset]=value
            with self.assertRaises(ROMError,msg=f'offset={offset}'):Cartridge(bad)

    def test_chr_ram_and_rom(self):
        n=self.machine();before=n.ppu.read_mem(0x401)
        n.ppu.write_mem(0x401,before^255);self.assertEqual(n.ppu.read_mem(0x401),before)
        data=bytearray(demo_rom()[:-8192]);data[5]=0
        n=NES(data);n.ppu.write_mem(0x401,0x75);self.assertEqual(n.ppu.read_mem(0x401),0x75)

    def test_nametable_mirroring(self):
        n=self.machine();p=n.ppu
        for mirror,expected in [('vertical',(1,2,1,2)),('horizontal',(1,1,2,2)),('four-screen',(1,2,3,4))]:
            n.cart.mirroring=mirror;p.nt[:]=b'\0'*4096
            for page,value in enumerate(expected):p.write_mem(0x2000+page*1024,value)
            self.assertEqual(tuple(p.read_mem(0x2000+page*1024) for page in range(4)),expected)
        p.write_mem(0x2011,0x87);self.assertEqual(p.read_mem(0x3011),0x87)

    def test_palette_aliases(self):
        p=self.machine().ppu
        for at in (0,4,8,12):
            p.write_mem(0x3f10+at,at+5)
            self.assertEqual(p.read_mem(0x3f00+at),at+5)
            self.assertEqual(p.read_mem(0x3f30+at),at+5)
        p.write_mem(0x3f01,255);self.assertEqual(p.read_mem(0x3f01),63)

    def test_register_latches_buffer_and_increment(self):
        p=self.machine().ppu
        p.write_mem(0x2100,0x42);p.write_mem(0x2101,0x18)
        p.write_register(6,0x21);p.write_register(6,0)
        self.assertEqual(p.read_register(7),0)
        self.assertEqual(p.read_register(7),0x42)
        self.assertEqual(p.read_register(7),0x18)
        p.write_register(0,4);p.write_register(6,0x22);p.write_register(6,0)
        p.write_register(7,0x51);self.assertEqual(p.v,0x2220)
        p.write_register(5,0x37);self.assertEqual(p.w,1)
        p.status=0xe0;p.read_register(2);self.assertEqual((p.w,p.status),(0,0x60))

    def test_palette_read_fills_buffer(self):
        p=self.machine().ppu;p.write_mem(0x3f00,0x22);p.write_mem(0x2f00,0x83)
        p.v=0x3f00;self.assertEqual(p.read_register(7),0x22);self.assertEqual(p.buffer,0x83)

    def test_scroll_wrap(self):
        p=self.machine().ppu;p.v=31;p.increment_x();self.assertEqual(p.v,0x400)
        p.v=0x7000|(29<<5);p.increment_y();self.assertEqual(p.v,0x800)
        p.v=0x7000|(31<<5);p.increment_y();self.assertEqual(p.v,0)
        p.v=0;p.increment_y();self.assertEqual(p.v,0x1000)
        p.write_register(5,0x2b);p.write_register(5,0x35)
        self.assertEqual(p.fine_x,3);self.assertEqual(p.t&31,5)
        self.assertEqual((p.t>>5)&31,6);self.assertEqual((p.t>>12)&7,5)

    def test_vblank_nmi_edge_and_status(self):
        n=self.machine();p=n.ppu
        p.tick(341-21)  # End initial pre-render line.
        p.write_register(0,128)
        p.tick(241*341)
        self.assertFalse(p.status&128)
        p.tick(1);self.assertTrue(p.status&128);self.assertTrue(n.cpu.nmi_pending)
        n.cpu.nmi_pending=False;p.write_register(0,128);self.assertFalse(n.cpu.nmi_pending)
        p.write_register(0,0);p.write_register(0,128);self.assertTrue(n.cpu.nmi_pending)
        self.assertTrue(p.read_register(2)&128);self.assertFalse(p.status&128)

    def test_oam_dma_wrap_and_timing(self):
        n=self.machine()
        n.cpu.pc=0;n.bus.ram[:2]=bytes([0xa9,2]);n.bus.ram[2:5]=bytes([0x8d,0x14,0x40])
        for i in range(256):n.bus.ram[0x200+i]=i
        n.ppu.oam_addr=7;n.step();before=n.cpu.cycles
        elapsed=n.step()
        self.assertEqual(elapsed,4+513+((before+4)&1))
        self.assertEqual(n.ppu.oam[7],0);self.assertEqual(n.ppu.oam[6],255)
        self.assertEqual(n.ppu.oam_addr,7)

    def test_controller_serial_latch(self):
        pad=Controller()
        for buttons in range(256):
            pad.buttons=buttons;pad.write(1)
            self.assertEqual(pad.read(),buttons&1)
            pad.write(0);pad.buttons=buttons^255
            self.assertEqual([pad.read() for _ in range(8)],[(buttons>>i)&1 for i in range(8)])
            self.assertEqual(pad.read(),1)

    def test_apu_status_and_irq(self):
        a=SilentAPU();a.write(0x4015,1);a.write(0x4003,0)
        self.assertEqual(a.read_status()&1,1)
        a.tick(29830);self.assertTrue(a.frame_irq)
        self.assertEqual(a.read_status()&64,64);self.assertFalse(a.frame_irq)
        a.write(0x4015,0);self.assertEqual(a.read_status()&15,0)
        a.write(0x4017,0x40);a.tick(29830);self.assertFalse(a.frame_irq)

    def graphics(self):
        data=bytearray(demo_rom()[:-8192]);data[5]=0
        n=NES(data);p=n.ppu
        p.oam[:]=b'\xff'*256
        p.mask=0x1e;p.palette[:]=bytes(range(32));p.palette[0]=15
        return p

    def test_background_attributes_and_left_clip(self):
        p=self.graphics();p.cart.chr[16:24]=b'\xff'*8
        p.write_mem(0x2000,1);p.write_mem(0x23c0,2)
        p.v=0;p.render_line(0)
        self.assertEqual(p.framebuffer[:8],bytes([9])*8)
        p.mask&=~2;p.render_line(0);self.assertEqual(p.framebuffer[:8],bytes([15])*8)

    def test_sprites_priority_flip_and_8x16(self):
        p=self.graphics();p.cart.chr[16]=128
        p.oam[:4]=bytes([9,1,0,20]);p.render_line(10)
        self.assertEqual(p.framebuffer[10*256+20],17)
        p.oam[2]=64;p.render_line(10)
        self.assertEqual(p.framebuffer[10*256+27],17)
        p.oam[2]=128;p.render_line(17)
        self.assertEqual(p.framebuffer[17*256+20],17)
        p.ctrl=32;p.oam[1]=3;p.oam[2]=0;p.cart.chr[0x1020]=128
        p.render_line(10);self.assertEqual(p.framebuffer[10*256+20],17)

    def test_sprite_zero_hit_and_overflow(self):
        p=self.graphics();p.cart.chr[16:24]=b'\xff'*8
        for x in range(32):p.write_mem(0x2000+x,1)
        p.oam[:4]=bytes([9,1,0,20]);p.v=0;p.render_line(10)
        self.assertEqual(p.sprite_hit_dot,21)
        p.scanline=10;p.dot=1;p.next_event=21;p.tick(19)
        self.assertFalse(p.status&64);p.tick(1);self.assertTrue(p.status&64)
        for i in range(9):p.oam[i*4:i*4+4]=bytes([9,1,0,20+i*8])
        p.render_line(10);self.assertTrue(p.status&32)

    def test_sprite_behind_background(self):
        p=self.graphics();p.cart.chr[16:24]=b'\xff'*8
        p.write_mem(0x2000,1);p.oam[:4]=bytes([0,1,32,0]);p.v=0;p.render_line(1)
        self.assertEqual(p.framebuffer[256],1)
        p.oam[2]=0;p.render_line(1);self.assertEqual(p.framebuffer[256],17)

    def test_render_cache_invalidation(self):
        p=self.graphics();p.cart.chr[16:24]=b'\xff'*8
        p.write_mem(0x2000,1);p.palette[1]=3;p.v=0;p.render_line(0)
        self.assertEqual(p.framebuffer[0],3)
        p.palette[1]=5;p.render_line(0);self.assertEqual(p.framebuffer[0],5)
        p.cart.chr[16:24]=b'\0'*8;p.cart.chr[24:32]=b'\xff'*8
        p.render_line(0);self.assertEqual(p.framebuffer[0],2)
        p.oam[:4]=bytes([9,1,0,20]);p.palette[18]=30;p.render_line(10)
        self.assertEqual(p.framebuffer[10*256+20],30)
        p.oam[3]=40;p.render_line(10)
        self.assertEqual(p.framebuffer[10*256+20],15)
        self.assertEqual(p.framebuffer[10*256+40],30)

    def test_rgb_cache_bound_and_invalidation(self):
        p=self.machine().ppu
        for frame in range(5):
            for y in range(240):
                value=frame*240+y
                p.framebuffer[y*256]=value&63
                p.framebuffer[y*256+1]=(value>>6)&63
            rgb=p.rgb_scaled()
            self.assertLessEqual(len(p.rgb_row_cache),1024)
            self.assertEqual(rgb[:3],PALETTE[(frame*240)&63])
            self.assertEqual(rgb[6:9],PALETTE[((frame*240)>>6)&63])

    def test_rgb_scaling(self):
        p=self.machine().ppu
        p.framebuffer[:]=bytes(i%64 for i in range(256*240))
        rgb=p.rgb_scaled()
        self.assertEqual(len(rgb),320*300*3)
        for y in (0,1,2,10,123,298,299):
            for x in (0,1,2,10,158,318,319):
                at=(y*320+x)*3
                self.assertEqual(rgb[at:at+3],PALETTE[p.framebuffer[(y*4//5)*256+x*4//5]])

    def test_demo_boot_movement_colors_and_reset(self):
        n=self.machine()
        for _ in range(10):n.frame()
        self.assertGreater(n.bus.ram[0],3)
        self.assertEqual((n.bus.ram[3],n.bus.ram[4]),(120,105))
        self.assertGreater(sum(c!=15 for c in n.ppu.framebuffer),2000)
        n.bus.controllers[0].set(7,True);n.bus.controllers[0].set(0,True)
        for _ in range(6):n.frame()
        self.assertEqual(n.bus.ram[3],126);self.assertEqual(n.bus.ram[5],0x29)
        self.assertEqual(n.ppu.palette[17],0x29)
        n.bus.controllers[0].buttons=1<<3
        for _ in range(3):n.frame()
        self.assertEqual((n.bus.ram[3],n.bus.ram[4]),(120,105))
        n.bus.write(0x6000,123);n.reset()
        self.assertEqual(n.bus.read(0x6000),0);self.assertEqual(n.ppu.frame,0)
        self.assertEqual(n.cpu.pc,0x8000)


def main(argv=None):
    parser=argparse.ArgumentParser(description='Blue NES: silent 600x400 Tkinter NTSC NROM emulator')
    parser.add_argument('rom',nargs='?',help='path to an extracted iNES mapper-0 .nes ROM')
    parser.add_argument('--demo',action='store_true',help='run the original built-in NROM demo')
    parser.add_argument('--self-test',action='store_true',help='run offline core regressions and exit; no Tk display needed')
    parser.add_argument('--headless',type=int,metavar='FRAMES',help='run this many frames without a GUI (demo if no ROM)')
    args=parser.parse_args(argv)
    if args.self_test:
        suite=unittest.defaultTestLoader.loadTestsFromTestCase(CoreTests)
        result=unittest.TextTestRunner(verbosity=2).run(suite)
        return 0 if result.wasSuccessful() else 1
    if args.rom and args.demo:parser.error('choose a ROM path or --demo, not both')
    if args.headless is not None and args.headless<=0:parser.error('--headless must be positive')
    data=None;name='BLUE NES / original demo'
    try:
        if args.rom:
            with open(args.rom,'rb') as stream:data=stream.read(Cartridge.MAX_SIZE+1)
            name=pathlib.Path(args.rom).name
            Cartridge(data,name)
        elif args.demo or args.headless is not None:data=demo_rom()
        if args.headless is not None:
            import hashlib
            n=NES(data,name);start=time.perf_counter()
            for _ in range(args.headless):n.frame()
            elapsed=time.perf_counter()-start
            print(f'{name}: {args.headless} frame(s), {n.cpu.cycles:,} CPU cycles, {elapsed:.3f}s')
            print(f'PC=${n.cpu.pc:04X}, framebuffer SHA256={hashlib.sha256(n.ppu.framebuffer).hexdigest()}')
            return 0
    except (OSError,ROMError,CPUError) as exc:
        print(f'Blue NES: {exc}',file=sys.stderr);return 1
    try:
        import tkinter as tk
        root=tk.Tk()
    except ImportError:
        print('Tkinter is missing. Install a Python distribution with Tcl/Tk (or python3-tk on Linux).',file=sys.stderr)
        return 1
    except tk.TclError as exc:
        print(f'Cannot open a Tk window: {exc}\nRun on a graphical desktop, or use --self-test / --demo --headless 60.',file=sys.stderr)
        return 1
    app=App(root)
    if data is not None:root.after(0,lambda:app.load_bytes(data,name))
    root.mainloop()
    return 0

if __name__=='__main__':
    raise SystemExit(main())
