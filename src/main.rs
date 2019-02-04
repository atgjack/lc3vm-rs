extern crate termios;
use termios::{Termios, TCSANOW, ECHO, ICANON, tcsetattr};
use std::io::Read;

const MEM_SIZE: usize = std::u16::MAX as usize;
const STDIN_FD: i32 = 0;

#[allow(dead_code)]
enum Register {
    R0 = 0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    PC,
    COND,
    COUNT
}

#[derive(Debug)]
enum OpCode {
    BR = 0,     /* branch */
    ADD,        /* add  */
    LD,         /* load */
    ST,         /* store */
    JSR,        /* jump register */
    AND,        /* bitwise and */
    LDR,        /* load register */
    STR,        /* store register */
    RTI,        /* unused */
    NOT,        /* bitwise not */
    LDI,        /* load indirect */
    STI,        /* store indirect */
    JMP,        /* jump */
    RES,        /* reserved (unused) */
    LEA,        /* load effective address */
    TRAP        /* execute trap */
}

impl OpCode {
    pub fn from_16(instr: u16) -> Self {
        match instr {
            x if x == OpCode::BR as u16 => OpCode::BR,
            x if x == OpCode::ADD as u16 => OpCode::ADD,
            x if x == OpCode::LD as u16 => OpCode::LD,
            x if x == OpCode::ST as u16 => OpCode::ST,
            x if x == OpCode::JSR as u16 => OpCode::JSR,
            x if x == OpCode::AND as u16 => OpCode::AND,
            x if x == OpCode::LDR as u16 => OpCode::LDR,
            x if x == OpCode::STR as u16 => OpCode::STR,
            x if x == OpCode::RTI as u16 => OpCode::RTI,
            x if x == OpCode::NOT as u16 => OpCode::NOT,
            x if x == OpCode::LDI as u16 => OpCode::LDI,
            x if x == OpCode::STI as u16 => OpCode::STI,
            x if x == OpCode::JMP as u16 => OpCode::JMP,
            x if x == OpCode::RES as u16 => OpCode::RES,
            x if x == OpCode::LEA as u16 => OpCode::LEA,
            x if x == OpCode::TRAP as u16 => OpCode::TRAP,
            _ => panic!("Out of range")
        }
    }
}

trait WithOpCodes {
    fn add(&mut self, instr: u16);
    fn and(&mut self, instr: u16);
    fn br(&mut self, instr: u16);
    fn jmp(&mut self, instr: u16);
    fn ldi(&mut self, instr: u16);
    fn jsr(&mut self, instr: u16);
    fn ld(&mut self, instr: u16);
    fn ldr(&mut self, instr: u16);
    fn lea(&mut self, instr: u16);
    fn not(&mut self, instr: u16);
    fn st(&mut self, instr: u16);
    fn sti(&mut self, instr: u16);
    fn str(&mut self, instr: u16);
    fn trap(&mut self, instr: u16);
}

enum TrapCode {
    GETC = 0x20,  /* get character from keyboard */
    OUT = 0x21,   /* output a character */
    PUTS = 0x22,  /* output a word string */
    IN = 0x23,    /* input a string */
    PUTSP = 0x24, /* output a byte string */
    HALT = 0x25   /* halt the program */
}

impl TrapCode {
    pub fn from_16(instr: u16) -> Self {
        match instr {
            x if x == TrapCode::GETC as u16 => TrapCode::GETC,
            x if x == TrapCode::OUT as u16 => TrapCode::OUT,
            x if x == TrapCode::PUTS as u16 => TrapCode::PUTS,
            x if x == TrapCode::IN as u16 => TrapCode::IN,
            x if x == TrapCode::PUTSP as u16 => TrapCode::PUTSP,
            x if x == TrapCode::HALT as u16 => TrapCode::HALT,
            _ => panic!("Out of range")
        }
    }
}

trait WithTrapCodes {
    fn getc(&mut self);
    fn out(&mut self);
    fn puts(&mut self);
    fn inp(&mut self);
    fn putsp(&mut self);
    fn halt(&mut self);
}

enum ConditionalFlags {
    POS = 1,
    ZRO = 1 << 1,
    NEG = 1 << 2
}

enum MemoryMappedRegisters {
    KBSR = 0xFE00, /* keyboard status */
    KBDR = 0xFE02  /* keyboard data */
}

const PC_START: u16 = 0x3000;

struct Vm {
    memory: [u16; MEM_SIZE],
    registers: [u16; 16],
    running: bool,
    termios: Termios
}

impl Drop for Vm {
    fn drop(&mut self) {
        tcsetattr(STDIN_FD, TCSANOW, & self.termios).unwrap();
    }
}

impl Vm {
    pub fn new() -> Self {
        let mut termios = Termios::from_fd(STDIN_FD).unwrap();
        let prev_flags = termios.c_lflag;
        termios.c_lflag &= !(ICANON | ECHO);
        tcsetattr(STDIN_FD, TCSANOW, &termios).unwrap();
        termios.c_lflag = prev_flags;

        Vm {
            memory: [0; MEM_SIZE],
            registers: [0; 16],
            termios: termios,
            running: false
        }
    }

    pub fn run(&mut self) {
        self.registers[Register::PC as usize] = PC_START;
        self.running = true;

        while self.running {
            self.run_loop()
        }
    }

    #[inline]
    fn run_loop(&mut self) {
        let instr = self.read_next_instr();
        
        match OpCode::from_16(instr >> 12) {
            OpCode::ADD => self.add(instr),
            OpCode::AND => self.and(instr),
            OpCode::BR  => self.br(instr), 
            OpCode::JMP => self.jmp(instr),
            OpCode::LDI => self.ldi(instr),
            OpCode::JSR => self.jsr(instr),
            OpCode::LD  => self.ld(instr),
            OpCode::LDR => self.ldr(instr),
            OpCode::LEA => self.lea(instr),
            OpCode::NOT => self.not(instr),
            OpCode::RTI => panic!("Unused opcode"),
            OpCode::RES => panic!("Unused opcode"),
            OpCode::ST => self.st(instr),
            OpCode::STI => self.sti(instr),
            OpCode::STR => self.str(instr),
            OpCode::TRAP => self.trap(instr)
        }
    }
    
    fn mem_read(&mut self, loc: u16) -> u16 {
        if loc == MemoryMappedRegisters::KBSR as u16 {
            let input = std::io::stdin().lock().bytes().next();

            if input.is_some() {
                self.memory[MemoryMappedRegisters::KBSR as usize] = 1 << 15;
                self.memory[MemoryMappedRegisters::KBDR as usize] = u16::from(input.unwrap().unwrap());
            } else {
                self.memory[MemoryMappedRegisters::KBSR as usize] = 0;
            }
        }

        self.memory[loc as usize]
    }

    fn mem_write(&mut self, loc: u16, data: u16) {
        self.memory[loc as usize] = data
    }

    #[inline]
    fn read_next_instr(&mut self) -> u16 {
        let instr = self.mem_read(self.registers[Register::PC as usize]);
        self.registers[Register::PC as usize] += 1;
        instr
    }

    fn update_flags(&mut self, r: u16) {
        self.registers[Register::COND as usize] = if self.registers[r as usize] == 0 {
            ConditionalFlags::ZRO
        } else if self.registers[r as usize] >> 15 != 0 {
            ConditionalFlags::NEG
        } else {
            ConditionalFlags::POS
        } as u16;
    }

    fn read_file(&mut self, file: &[u8]) {
        let origin = (u16::from(file[0]) << 8) | u16::from(file[1]);
        
        file.iter()
            .skip(2)
            .scan(None, scan_combine_u8_to_u16)
            .filter_map(|o| o)
            .map(|b| b.swap())
            .enumerate()
            .for_each(|(index, data)| self.mem_write(origin + (index as u16), data));
    }

    fn read_image(&mut self, filename: &str) {
        self.read_file(&std::fs::read(filename).unwrap())
    }
}

#[inline]
fn scan_combine_u8_to_u16(o: &mut Option<u8>, input: &u8) -> Option<Option<u16>> {
    match o {
        Some(p) => {
            let prev = u16::from(*p);
            let next = u16::from(*input) << 8;
            *o = None;
            Some(Some(prev + next))
        },
        None => {
            *o = Some(*input);
            Some(None)
        }
    }
}

impl WithOpCodes for Vm {
    fn add(&mut self, instr: u16) {
        let dr = (instr >> 9) & 0x7; 
        let r1 = (instr >> 6) & 0x7;
        let imm_flag = (instr >> 5) & 0x1 != 0;

        if imm_flag {
            let imm5 = (instr & 0x1F).sign_extend(5);
            self.registers[dr as usize] = self.registers[r1 as usize].wrapping_add(imm5);
        } else {
            let r2 = instr & 0x7;
            self.registers[dr as usize] = self.registers[r1 as usize].wrapping_add(self.registers[r2 as usize]);
        }

        self.update_flags(dr);
    }

    fn and(&mut self, instr: u16) {
        let dr = (instr >> 9) & 0x7; 
        let sr1 = (instr >> 6) & 0x7;
        let imm_flag = (instr >> 5) & 0x1 != 0;

        if imm_flag {
            let imm5 = (instr & 0x1F).sign_extend(5);
            self.registers[dr as usize] = self.registers[sr1 as usize] & imm5;
        } else {
            let sr2 = instr & 0x7;
            self.registers[dr as usize] = self.registers[sr1 as usize] & self.registers[sr2 as usize];
        }

        self.update_flags(dr);
    }

    fn br(&mut self, instr: u16) {
        let cond_flag = (instr >> 9) & 0x7;
        
        if (cond_flag & self.registers[Register::COND as usize]) != 0 {
            let pc_offset = (instr & 0x1FF).sign_extend(9);
            self.registers[Register::PC as usize] = self.registers[Register::PC as usize].wrapping_add(pc_offset);
        }
    }

    fn jmp(&mut self, instr: u16) {
        let base_r = (instr >> 6) & 0x7;
        self.registers[Register::PC as usize] = self.registers[base_r as usize];
    }

    fn jsr(&mut self, instr: u16) {
        self.registers[Register::R7 as usize] = self.registers[Register::PC as usize];
        let jmp_flag = (instr >> 11) & 0x1 == 0;
        if jmp_flag {
            let base_r = (instr >> 6) & 0x7;
            self.registers[Register::PC as usize] = self.registers[base_r as usize];
        } else {
            let pc_offset = (instr & 0x7FF).sign_extend(11);
            self.registers[Register::PC as usize] = self.registers[Register::PC as usize].wrapping_add(pc_offset);
        }
    }

    fn ld(&mut self, instr: u16) {
        let dr = (instr >> 9) & 0x7;
        let pc_offset = (instr & 0x1FF).sign_extend(9);

        self.registers[dr as usize] = self.mem_read(self.registers[Register::PC as usize].wrapping_add(pc_offset));
        
        self.update_flags(dr)
    }

    fn ldi(&mut self, instr: u16) {
        let dr = (instr >> 9) & 0x7;
        let pc_offset = (instr & 0x1FF).sign_extend(9);

        let loc = self.mem_read(self.registers[Register::PC as usize].wrapping_add(pc_offset));
        self.registers[dr as usize] = self.mem_read(loc);

        self.update_flags(dr);
    }

    fn ldr(&mut self, instr: u16) {
        let dr = (instr >> 9) & 0x7;
        let base_r = (instr >> 6) & 0x7;
        let offset = (instr & 0x3F).sign_extend(6);

        self.registers[dr as usize] = self.mem_read(self.registers[base_r as usize].wrapping_add(offset));

        self.update_flags(dr);
    }

    fn lea(&mut self, instr: u16) {
        let dr = (instr >> 9) & 0x7;
        let pc_offset = (instr & 0x1FF).sign_extend(9);

        self.registers[dr as usize] = self.registers[Register::PC as usize].wrapping_add(pc_offset);

        self.update_flags(dr);
    }

    fn not(&mut self, instr: u16) {
        let dr = (instr >> 9) & 0x7;
        let sr = (instr >> 6) & 0x7;

        self.registers[dr as usize] = !self.registers[sr as usize];

        self.update_flags(dr);
    }

    fn st(&mut self, instr: u16) {
        let sr = (instr >> 9) & 0x7;
        let pc_offset = (instr & 0x1FF).sign_extend(9);

        self.mem_write(self.registers[Register::PC as usize].wrapping_add(pc_offset), self.registers[sr as usize]);
    }

    fn sti(&mut self, instr: u16) {
        let sr = (instr >> 9) & 0x7;
        let pc_offset = (instr & 0x1FF).sign_extend(9);

        let loc = self.mem_read(self.registers[Register::PC as usize].wrapping_add(pc_offset));
        self.mem_write(loc, self.registers[sr as usize]);
    }

    fn str(&mut self, instr: u16) {
        let sr = (instr >> 9) & 0x7;
        let base_r = (instr >> 6) & 0x7;
        let offset = (instr & 0x3F).sign_extend(6);

        self.mem_write(self.registers[base_r as usize].wrapping_add(offset), self.registers[sr as usize]);
    }

    fn trap(&mut self, instr: u16) {
        match TrapCode::from_16(instr & 0xFF) {
            TrapCode::GETC => self.getc(),
            TrapCode::OUT => self.out(),
            TrapCode::PUTS => self.puts(),
            TrapCode::IN => self.inp(),
            TrapCode::PUTSP => self.putsp(),
            TrapCode::HALT => self.halt(),
        }
    }
}

impl WithTrapCodes for Vm {
    fn getc(&mut self) {
        self.registers[Register::R0 as usize] = std::io::stdin()
            .lock()
            .bytes()
            .next()
            .unwrap()
            .map(u16::from)
            .unwrap();
    }

    fn out(&mut self) {
        print!("{}", self.registers[Register::R0 as usize] as u8 as char)
    }

    fn puts(&mut self) {
        self.memory[(self.registers[Register::R0 as usize] as usize)..]
            .iter()
            .take_while(|&b| *b != 0)
            .map(|b| *b as u8)
            .map(|b| b as char)
            .for_each(|c| print!("{}", c));
    }

    fn inp(&mut self) {
        println!("Enter a character: ");
        self.getc()
    }

    fn putsp(&mut self) {
        self.memory[(self.registers[Register::R0 as usize] as usize)..]
            .iter()
            .take_while(|&b| *b != 0)
            .map(|&b| ((b & 0xFF) as u8, (b >> 8) as u8))
            .for_each(|(c1, c2)| {
                print!("{}", c1 as char);
                if c2 != 0 {
                    print!("{}", c2 as char)
                }
            });
    }

    fn halt(&mut self) {
        println!("HALT");
        self.running = false;
    }

}

trait SwapEndian {
    fn swap(self) -> Self;
}

impl SwapEndian for u16 {
    fn swap(self) -> Self {
        (self << 8) | (self >> 8)
    }
}

trait SignExtend {
    fn sign_extend(self, bit_count: usize) -> Self;
}

impl SignExtend for u16 {
    fn sign_extend(self, bit_count: usize) -> Self {
        if (self >> (bit_count - 1)) & 1 != 0 {
            self | (0xFFFF << bit_count)
        } else {
            self
        }
    }
}

fn main() {
    let mut vm = Vm::new();

    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        println!("lc3 [image-file1] ...");
    }

    vm.read_image(&args[1]);

    vm.run();
}
