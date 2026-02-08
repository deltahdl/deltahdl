#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "common/source_loc.h"

namespace delta {

enum class TokenKind {
  // Sentinel
  Eof = 0,
  Error,

  // Literals
  IntLiteral,
  RealLiteral,
  TimeLiteral,
  StringLiteral,
  UnbasedUnsizedLiteral,  // '0, '1, 'x, 'z

  // Identifiers
  Identifier,
  EscapedIdentifier,
  SystemIdentifier,  // $display, $finish, etc.

  // Operators and punctuation
  Plus,            // +
  Minus,           // -
  Star,            // *
  Slash,           // /
  Percent,         // %
  Power,           // **
  Amp,             // &
  Pipe,            // |
  Caret,           // ^
  Tilde,           // ~
  TildeAmp,        // ~&
  TildePipe,       // ~|
  TildeCaret,      // ~^
  CaretTilde,      // ^~
  AmpAmp,          // &&
  PipePipe,        // ||
  Bang,            // !
  Eq,              // =
  EqEq,            // ==
  BangEq,          // !=
  EqEqEq,          // ===
  BangEqEq,        // !==
  EqEqQuestion,    // ==?
  BangEqQuestion,  // !=?
  Lt,              // <
  Gt,              // >
  LtEq,            // <=
  GtEq,            // >=
  LtLt,            // <<
  GtGt,            // >>
  LtLtLt,          // <<<
  GtGtGt,          // >>>
  PlusPlus,        // ++
  MinusMinus,      // --
  PlusEq,          // +=
  MinusEq,         // -=
  StarEq,          // *=
  SlashEq,         // /=
  PercentEq,       // %=
  AmpEq,           // &=
  PipeEq,          // |=
  CaretEq,         // ^=
  LtLtEq,          // <<=
  GtGtEq,          // >>=
  LtLtLtEq,        // <<<=
  GtGtGtEq,        // >>>=
  Question,        // ?
  Colon,           // :
  ColonColon,      // ::
  Semicolon,       // ;
  Comma,           // ,
  Dot,             // .
  DotStar,         // .*
  LParen,          // (
  RParen,          // )
  LBracket,        // [
  RBracket,        // ]
  LBrace,          // {
  RBrace,          // }
  Hash,            // #
  HashHash,        // ##
  At,              // @
  AtAt,            // @@
  Arrow,           // ->
  DashGtGt,        // ->>
  EqGt,            // =>
  StarGt,          // *>
  AmpAmpAmp,       // &&&
  PipeDashGt,      // |->
  PipeEqGt,        // |=>
  HashMinusHash,   // #-#
  HashEqHash,      // #=#

  // Keywords start here (mapped by keywords table)
  KwModule,
  KwEndmodule,
  KwInput,
  KwOutput,
  KwInout,
  KwRef,
  KwWire,
  KwReg,
  KwLogic,
  KwBit,
  KwByte,
  KwShortint,
  KwInt,
  KwLongint,
  KwInteger,
  KwReal,
  KwShortreal,
  KwRealtime,
  KwTime,
  KwString,
  KwChandle,
  KwVoid,
  KwEnum,
  KwStruct,
  KwUnion,
  KwTypedef,
  KwClass,
  KwExtends,
  KwInterface,
  KwEndinterface,
  KwPackage,
  KwEndpackage,
  KwProgram,
  KwEndprogram,
  KwParameter,
  KwLocalparam,
  KwSpecparam,
  KwAssign,
  KwDeassign,
  KwAlways,
  KwAlwaysComb,
  KwAlwaysFF,
  KwAlwaysLatch,
  KwInitial,
  KwFinal,
  KwBegin,
  KwEnd,
  KwFork,
  KwJoin,
  KwJoinAny,
  KwJoinNone,
  KwIf,
  KwElse,
  KwCase,
  KwCasex,
  KwCasez,
  KwEndcase,
  KwFor,
  KwForever,
  KwWhile,
  KwDo,
  KwRepeat,
  KwBreak,
  KwContinue,
  KwReturn,
  KwFunction,
  KwEndfunction,
  KwTask,
  KwEndtask,
  KwGenerate,
  KwEndgenerate,
  KwGenvar,
  KwPosedge,
  KwNegedge,
  KwEdge,
  KwOr,
  KwAnd,
  KwNot,
  KwSupply0,
  KwSupply1,
  KwTri,
  KwTriand,
  KwTrior,
  KwTri0,
  KwTri1,
  KwTrireg,
  KwWand,
  KwWor,
  KwUwire,
  KwSigned,
  KwUnsigned,
  KwAutomatic,
  KwStatic,
  KwConst,
  KwVar,
  KwImport,
  KwExport,
  KwForce,
  KwRelease,
  KwWait,
  KwDisable,
  KwNull,
  KwThis,
  KwSuper,
  KwNew,
  KwPacked,
  KwTagged,
  KwDefault,
  KwUnique,
  KwUnique0,
  KwPriority,
  // Add more keywords as needed (there are ~260 total)
};

struct Token {
  TokenKind kind = TokenKind::Eof;
  SourceLoc loc;
  std::string_view text;

  // For integer literals
  uint32_t bit_width = 0;
  bool has_size = false;
  bool is_signed = false;
  uint8_t base = 10;  // 2, 8, 10, 16

  bool is(TokenKind k) const { return kind == k; }
  bool is_eof() const { return kind == TokenKind::Eof; }
};

std::string_view token_kind_name(TokenKind kind);

}  // namespace delta
