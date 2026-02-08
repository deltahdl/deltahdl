#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "common/source_loc.h"

namespace delta {

enum class TokenKind : uint8_t {
  // Sentinel
  kEof = 0,
  kError,

  // Literals
  kIntLiteral,
  kRealLiteral,
  kTimeLiteral,
  kStringLiteral,
  kUnbasedUnsizedLiteral,  // '0, '1, 'x, 'z

  // Identifiers
  kIdentifier,
  kEscapedIdentifier,
  kSystemIdentifier,  // $display, $finish, etc.

  // Operators and punctuation
  kPlus,            // +
  kMinus,           // -
  kStar,            // *
  kSlash,           // /
  kPercent,         // %
  kPower,           // **
  kAmp,             // &
  kPipe,            // |
  kCaret,           // ^
  kTilde,           // ~
  kTildeAmp,        // ~&
  kTildePipe,       // ~|
  kTildeCaret,      // ~^
  kCaretTilde,      // ^~
  kAmpAmp,          // &&
  kPipePipe,        // ||
  kBang,            // !
  kEq,              // =
  kEqEq,            // ==
  kBangEq,          // !=
  kEqEqEq,          // ===
  kBangEqEq,        // !==
  kEqEqQuestion,    // ==?
  kBangEqQuestion,  // !=?
  kLt,              // <
  kGt,              // >
  kLtEq,            // <=
  kGtEq,            // >=
  kLtLt,            // <<
  kGtGt,            // >>
  kLtLtLt,          // <<<
  kGtGtGt,          // >>>
  kPlusPlus,        // ++
  kMinusMinus,      // --
  kPlusEq,          // +=
  kMinusEq,         // -=
  kStarEq,          // *=
  kSlashEq,         // /=
  kPercentEq,       // %=
  kAmpEq,           // &=
  kPipeEq,          // |=
  kCaretEq,         // ^=
  kLtLtEq,          // <<=
  kGtGtEq,          // >>=
  kLtLtLtEq,        // <<<=
  kGtGtGtEq,        // >>>=
  kQuestion,        // ?
  kColon,           // :
  kColonColon,      // ::
  kSemicolon,       // ;
  kComma,           // ,
  kDot,             // .
  kDotStar,         // .*
  kLParen,          // (
  kRParen,          // )
  kLBracket,        // [
  kRBracket,        // ]
  kLBrace,          // {
  kRBrace,          // }
  kHash,            // #
  kHashHash,        // ##
  kAt,              // @
  kAtAt,            // @@
  kArrow,           // ->
  kDashGtGt,        // ->>
  kEqGt,            // =>
  kStarGt,          // *>
  kAmpAmpAmp,       // &&&
  kPipeDashGt,      // |->
  kPipeEqGt,        // |=>
  kHashMinusHash,   // #-#
  kHashEqHash,      // #=#

  // Keywords start here (mapped by keywords table)
  kKwModule,
  kKwEndmodule,
  kKwInput,
  kKwOutput,
  kKwInout,
  kKwRef,
  kKwWire,
  kKwReg,
  kKwLogic,
  kKwBit,
  kKwByte,
  kKwShortint,
  kKwInt,
  kKwLongint,
  kKwInteger,
  kKwReal,
  kKwShortreal,
  kKwRealtime,
  kKwTime,
  kKwString,
  kKwChandle,
  kKwVoid,
  kKwEnum,
  kKwStruct,
  kKwUnion,
  kKwTypedef,
  kKwClass,
  kKwExtends,
  kKwInterface,
  kKwEndinterface,
  kKwPackage,
  kKwEndpackage,
  kKwProgram,
  kKwEndprogram,
  kKwParameter,
  kKwLocalparam,
  kKwSpecparam,
  kKwAssign,
  kKwDeassign,
  kKwAlways,
  kKwAlwaysComb,
  kKwAlwaysFF,
  kKwAlwaysLatch,
  kKwInitial,
  kKwFinal,
  kKwBegin,
  kKwEnd,
  kKwFork,
  kKwJoin,
  kKwJoinAny,
  kKwJoinNone,
  kKwIf,
  kKwElse,
  kKwCase,
  kKwCasex,
  kKwCasez,
  kKwEndcase,
  kKwFor,
  kKwForever,
  kKwWhile,
  kKwDo,
  kKwRepeat,
  kKwBreak,
  kKwContinue,
  kKwReturn,
  kKwFunction,
  kKwEndfunction,
  kKwTask,
  kKwEndtask,
  kKwGenerate,
  kKwEndgenerate,
  kKwGenvar,
  kKwPosedge,
  kKwNegedge,
  kKwEdge,
  kKwOr,
  kKwAnd,
  kKwNot,
  kKwSupply0,
  kKwSupply1,
  kKwTri,
  kKwTriand,
  kKwTrior,
  kKwTri0,
  kKwTri1,
  kKwTrireg,
  kKwWand,
  kKwWor,
  kKwUwire,
  kKwSigned,
  kKwUnsigned,
  kKwAutomatic,
  kKwStatic,
  kKwConst,
  kKwVar,
  kKwImport,
  kKwExport,
  kKwForce,
  kKwRelease,
  kKwWait,
  kKwDisable,
  kKwNull,
  kKwThis,
  kKwSuper,
  kKwNew,
  kKwPacked,
  kKwTagged,
  kKwDefault,
  kKwUnique,
  kKwUnique0,
  kKwPriority,
  // Add more keywords as needed (there are ~260 total)
};

struct Token {
  TokenKind kind = TokenKind::kEof;
  SourceLoc loc;
  std::string_view text;

  // For integer literals
  uint32_t bit_width = 0;
  bool has_size = false;
  bool is_signed = false;
  uint8_t base = 10;  // 2, 8, 10, 16

  bool Is(TokenKind k) const { return kind == k; }
  bool IsEof() const { return kind == TokenKind::kEof; }
};

std::string_view TokenKindName(TokenKind kind);

}  // namespace delta
