use crate::types::Sort;

pub const EXPR_MAGIC: [u8; 4] = *b"SMT\0";
pub const REQUEST_MAGIC: [u8; 4] = *b"SMTQ";
pub const RESPONSE_MAGIC: [u8; 4] = *b"SMTR";
pub const VERSION: u8 = 1;

pub const EXPR_HEADER_LEN: usize = 32;
pub const NODE_RECORD_LEN: usize = 24;
pub const REQUEST_ENVELOPE_LEN: usize = 32;
pub const RESPONSE_ENVELOPE_LEN: usize = 16;

pub mod tag {
    pub const BV_VAR: u8 = 0;
    pub const BV_CONST: u8 = 1;
    pub const BV_NOT: u8 = 2;
    pub const BV_NEG: u8 = 3;
    pub const BV_AND: u8 = 4;
    pub const BV_OR: u8 = 5;
    pub const BV_XOR: u8 = 6;
    pub const BV_ADD: u8 = 7;
    pub const BV_SUB: u8 = 8;
    pub const BV_MUL: u8 = 9;
    pub const BV_UDIV: u8 = 10;
    pub const BV_UREM: u8 = 11;
    pub const BV_SDIV: u8 = 12;
    pub const BV_SREM: u8 = 13;
    pub const BV_SMOD: u8 = 14;
    pub const BV_SHL: u8 = 15;
    pub const BV_LSHR: u8 = 16;
    pub const BV_ASHR: u8 = 17;
    pub const BV_EXTRACT: u8 = 18;
    pub const BV_CONCAT: u8 = 19;
    pub const BV_ZEXT: u8 = 20;
    pub const BV_SEXT: u8 = 21;
    pub const BV_ITE: u8 = 22;
    pub const BV_SELECT: u8 = 23;
    pub const BOOL_TRUE: u8 = 24;
    pub const BOOL_FALSE: u8 = 25;
    pub const BOOL_VAR: u8 = 26;
    pub const BOOL_NOT: u8 = 27;
    pub const BOOL_AND: u8 = 28;
    pub const BOOL_OR: u8 = 29;
    pub const BOOL_IMPLIES: u8 = 30;
    pub const BV_EQ: u8 = 31;
    pub const BV_ULT: u8 = 32;
    pub const BV_ULE: u8 = 33;
    pub const BV_SLT: u8 = 34;
    pub const BV_SLE: u8 = 35;
    pub const UADD_OVF: u8 = 36;
    pub const SADD_OVF: u8 = 37;
    pub const USUB_OVF: u8 = 38;
    pub const SSUB_OVF: u8 = 39;
    pub const UMUL_OVF: u8 = 40;
    pub const SMUL_OVF: u8 = 41;
    pub const NEG_OVF: u8 = 42;
    pub const SDIV_OVF: u8 = 43;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Tag {
    BvVar = tag::BV_VAR,
    BvConst = tag::BV_CONST,
    BvNot = tag::BV_NOT,
    BvNeg = tag::BV_NEG,
    BvAnd = tag::BV_AND,
    BvOr = tag::BV_OR,
    BvXor = tag::BV_XOR,
    BvAdd = tag::BV_ADD,
    BvSub = tag::BV_SUB,
    BvMul = tag::BV_MUL,
    BvUdiv = tag::BV_UDIV,
    BvUrem = tag::BV_UREM,
    BvSdiv = tag::BV_SDIV,
    BvSrem = tag::BV_SREM,
    BvSmod = tag::BV_SMOD,
    BvShl = tag::BV_SHL,
    BvLshr = tag::BV_LSHR,
    BvAshr = tag::BV_ASHR,
    BvExtract = tag::BV_EXTRACT,
    BvConcat = tag::BV_CONCAT,
    BvZext = tag::BV_ZEXT,
    BvSext = tag::BV_SEXT,
    BvIte = tag::BV_ITE,
    BvSelect = tag::BV_SELECT,
    BoolTrue = tag::BOOL_TRUE,
    BoolFalse = tag::BOOL_FALSE,
    BoolVar = tag::BOOL_VAR,
    BoolNot = tag::BOOL_NOT,
    BoolAnd = tag::BOOL_AND,
    BoolOr = tag::BOOL_OR,
    BoolImplies = tag::BOOL_IMPLIES,
    BvEq = tag::BV_EQ,
    BvUlt = tag::BV_ULT,
    BvUle = tag::BV_ULE,
    BvSlt = tag::BV_SLT,
    BvSle = tag::BV_SLE,
    UaddOvf = tag::UADD_OVF,
    SaddOvf = tag::SADD_OVF,
    UsubOvf = tag::USUB_OVF,
    SsubOvf = tag::SSUB_OVF,
    UmulOvf = tag::UMUL_OVF,
    SmulOvf = tag::SMUL_OVF,
    NegOvf = tag::NEG_OVF,
    SdivOvf = tag::SDIV_OVF,
}

impl TryFrom<u8> for Tag {
    type Error = ();

    fn try_from(value: u8) -> core::result::Result<Self, Self::Error> {
        Ok(match value {
            tag::BV_VAR => Tag::BvVar,
            tag::BV_CONST => Tag::BvConst,
            tag::BV_NOT => Tag::BvNot,
            tag::BV_NEG => Tag::BvNeg,
            tag::BV_AND => Tag::BvAnd,
            tag::BV_OR => Tag::BvOr,
            tag::BV_XOR => Tag::BvXor,
            tag::BV_ADD => Tag::BvAdd,
            tag::BV_SUB => Tag::BvSub,
            tag::BV_MUL => Tag::BvMul,
            tag::BV_UDIV => Tag::BvUdiv,
            tag::BV_UREM => Tag::BvUrem,
            tag::BV_SDIV => Tag::BvSdiv,
            tag::BV_SREM => Tag::BvSrem,
            tag::BV_SMOD => Tag::BvSmod,
            tag::BV_SHL => Tag::BvShl,
            tag::BV_LSHR => Tag::BvLshr,
            tag::BV_ASHR => Tag::BvAshr,
            tag::BV_EXTRACT => Tag::BvExtract,
            tag::BV_CONCAT => Tag::BvConcat,
            tag::BV_ZEXT => Tag::BvZext,
            tag::BV_SEXT => Tag::BvSext,
            tag::BV_ITE => Tag::BvIte,
            tag::BV_SELECT => Tag::BvSelect,
            tag::BOOL_TRUE => Tag::BoolTrue,
            tag::BOOL_FALSE => Tag::BoolFalse,
            tag::BOOL_VAR => Tag::BoolVar,
            tag::BOOL_NOT => Tag::BoolNot,
            tag::BOOL_AND => Tag::BoolAnd,
            tag::BOOL_OR => Tag::BoolOr,
            tag::BOOL_IMPLIES => Tag::BoolImplies,
            tag::BV_EQ => Tag::BvEq,
            tag::BV_ULT => Tag::BvUlt,
            tag::BV_ULE => Tag::BvUle,
            tag::BV_SLT => Tag::BvSlt,
            tag::BV_SLE => Tag::BvSle,
            tag::UADD_OVF => Tag::UaddOvf,
            tag::SADD_OVF => Tag::SaddOvf,
            tag::USUB_OVF => Tag::UsubOvf,
            tag::SSUB_OVF => Tag::SsubOvf,
            tag::UMUL_OVF => Tag::UmulOvf,
            tag::SMUL_OVF => Tag::SmulOvf,
            tag::NEG_OVF => Tag::NegOvf,
            tag::SDIV_OVF => Tag::SdivOvf,
            _ => return Err(()),
        })
    }
}

impl From<Tag> for u8 {
    fn from(value: Tag) -> Self {
        value as u8
    }
}

impl Tag {
    pub const fn name(self) -> &'static str {
        match self {
            Tag::BvVar => "BV_VAR",
            Tag::BvConst => "BV_CONST",
            Tag::BvNot => "BV_NOT",
            Tag::BvNeg => "BV_NEG",
            Tag::BvAnd => "BV_AND",
            Tag::BvOr => "BV_OR",
            Tag::BvXor => "BV_XOR",
            Tag::BvAdd => "BV_ADD",
            Tag::BvSub => "BV_SUB",
            Tag::BvMul => "BV_MUL",
            Tag::BvUdiv => "BV_UDIV",
            Tag::BvUrem => "BV_UREM",
            Tag::BvSdiv => "BV_SDIV",
            Tag::BvSrem => "BV_SREM",
            Tag::BvSmod => "BV_SMOD",
            Tag::BvShl => "BV_SHL",
            Tag::BvLshr => "BV_LSHR",
            Tag::BvAshr => "BV_ASHR",
            Tag::BvExtract => "BV_EXTRACT",
            Tag::BvConcat => "BV_CONCAT",
            Tag::BvZext => "BV_ZEXT",
            Tag::BvSext => "BV_SEXT",
            Tag::BvIte => "BV_ITE",
            Tag::BvSelect => "BV_SELECT",
            Tag::BoolTrue => "BOOL_TRUE",
            Tag::BoolFalse => "BOOL_FALSE",
            Tag::BoolVar => "BOOL_VAR",
            Tag::BoolNot => "BOOL_NOT",
            Tag::BoolAnd => "BOOL_AND",
            Tag::BoolOr => "BOOL_OR",
            Tag::BoolImplies => "BOOL_IMPLIES",
            Tag::BvEq => "BV_EQ",
            Tag::BvUlt => "BV_ULT",
            Tag::BvUle => "BV_ULE",
            Tag::BvSlt => "BV_SLT",
            Tag::BvSle => "BV_SLE",
            Tag::UaddOvf => "UADD_OVF",
            Tag::SaddOvf => "SADD_OVF",
            Tag::UsubOvf => "USUB_OVF",
            Tag::SsubOvf => "SSUB_OVF",
            Tag::UmulOvf => "UMUL_OVF",
            Tag::SmulOvf => "SMUL_OVF",
            Tag::NegOvf => "NEG_OVF",
            Tag::SdivOvf => "SDIV_OVF",
        }
    }

    pub const fn result_sort(self) -> Sort {
        match self {
            Tag::BvVar
            | Tag::BvConst
            | Tag::BvNot
            | Tag::BvNeg
            | Tag::BvAnd
            | Tag::BvOr
            | Tag::BvXor
            | Tag::BvAdd
            | Tag::BvSub
            | Tag::BvMul
            | Tag::BvUdiv
            | Tag::BvUrem
            | Tag::BvSdiv
            | Tag::BvSrem
            | Tag::BvSmod
            | Tag::BvShl
            | Tag::BvLshr
            | Tag::BvAshr
            | Tag::BvExtract
            | Tag::BvConcat
            | Tag::BvZext
            | Tag::BvSext
            | Tag::BvIte
            | Tag::BvSelect => Sort::Bv,
            _ => Sort::Bool,
        }
    }

    pub const fn fixed_arity(self) -> Option<u8> {
        Some(match self {
            Tag::BvVar | Tag::BvConst | Tag::BoolTrue | Tag::BoolFalse | Tag::BoolVar => 0,
            Tag::BvNot
            | Tag::BvNeg
            | Tag::BvExtract
            | Tag::BvZext
            | Tag::BvSext
            | Tag::BoolNot
            | Tag::NegOvf => 1,
            Tag::BvAnd
            | Tag::BvOr
            | Tag::BvXor
            | Tag::BvAdd
            | Tag::BvSub
            | Tag::BvMul
            | Tag::BvUdiv
            | Tag::BvUrem
            | Tag::BvSdiv
            | Tag::BvSrem
            | Tag::BvSmod
            | Tag::BvShl
            | Tag::BvLshr
            | Tag::BvAshr
            | Tag::BvConcat
            | Tag::BoolAnd
            | Tag::BoolOr
            | Tag::BoolImplies
            | Tag::BvEq
            | Tag::BvUlt
            | Tag::BvUle
            | Tag::BvSlt
            | Tag::BvSle
            | Tag::UaddOvf
            | Tag::SaddOvf
            | Tag::UsubOvf
            | Tag::SsubOvf
            | Tag::UmulOvf
            | Tag::SmulOvf
            | Tag::SdivOvf => 2,
            Tag::BvIte => 3,
            Tag::BvSelect => return None,
        })
    }
}

pub mod command {
    pub const SOLVE: u8 = 0;
    pub const SIMPLIFY: u8 = 1;
    pub const MINIMIZE: u8 = 2;
    pub const MAXIMIZE: u8 = 3;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Command {
    Solve = command::SOLVE,
    Simplify = command::SIMPLIFY,
    Minimize = command::MINIMIZE,
    Maximize = command::MAXIMIZE,
}

impl TryFrom<u8> for Command {
    type Error = ();

    fn try_from(value: u8) -> core::result::Result<Self, Self::Error> {
        Ok(match value {
            command::SOLVE => Command::Solve,
            command::SIMPLIFY => Command::Simplify,
            command::MINIMIZE => Command::Minimize,
            command::MAXIMIZE => Command::Maximize,
            _ => return Err(()),
        })
    }
}

impl From<Command> for u8 {
    fn from(value: Command) -> Self {
        value as u8
    }
}

pub mod request_flags {
    pub const WANT_MODEL: u8 = 1 << 0;
    pub const WANT_CORE: u8 = 1 << 1;
    pub const SIGNED: u8 = 1 << 2;
    pub const ALL: u8 = WANT_MODEL | WANT_CORE | SIGNED;
}

pub mod status {
    pub const OK: u8 = 0;
    pub const SAT: u8 = 1;
    pub const UNSAT: u8 = 2;
    pub const UNKNOWN: u8 = 3;
    pub const ERROR: u8 = 4;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Status {
    Ok = status::OK,
    Sat = status::SAT,
    Unsat = status::UNSAT,
    Unknown = status::UNKNOWN,
    Error = status::ERROR,
}

impl TryFrom<u8> for Status {
    type Error = ();

    fn try_from(value: u8) -> core::result::Result<Self, ()> {
        Ok(match value {
            status::OK => Status::Ok,
            status::SAT => Status::Sat,
            status::UNSAT => Status::Unsat,
            status::UNKNOWN => Status::Unknown,
            status::ERROR => Status::Error,
            _ => return Err(()),
        })
    }
}

impl From<Status> for u8 {
    fn from(value: Status) -> Self {
        value as u8
    }
}

pub mod response_flags {
    pub const HAS_MODEL: u8 = 1 << 0;
    pub const HAS_CORE: u8 = 1 << 1;
    pub const HAS_EXPR: u8 = 1 << 2;
    pub const HAS_VALUE: u8 = 1 << 3;
    pub const HAS_MESSAGE: u8 = 1 << 4;
    pub const ALL: u8 = HAS_MODEL | HAS_CORE | HAS_EXPR | HAS_VALUE | HAS_MESSAGE;
}
