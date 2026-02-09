#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "common/source_loc.h"

namespace delta {

enum class TokenKind : uint16_t {
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
  kPlus,              // +
  kMinus,             // -
  kStar,              // *
  kSlash,             // /
  kPercent,           // %
  kPower,             // **
  kAmp,               // &
  kPipe,              // |
  kCaret,             // ^
  kTilde,             // ~
  kTildeAmp,          // ~&
  kTildePipe,         // ~|
  kTildeCaret,        // ~^
  kCaretTilde,        // ^~
  kAmpAmp,            // &&
  kPipePipe,          // ||
  kBang,              // !
  kEq,                // =
  kEqEq,              // ==
  kBangEq,            // !=
  kEqEqEq,            // ===
  kBangEqEq,          // !==
  kEqEqQuestion,      // ==?
  kBangEqQuestion,    // !=?
  kLt,                // <
  kGt,                // >
  kLtEq,              // <=
  kGtEq,              // >=
  kLtLt,              // <<
  kGtGt,              // >>
  kLtLtLt,            // <<<
  kGtGtGt,            // >>>
  kPlusPlus,          // ++
  kMinusMinus,        // --
  kPlusEq,            // +=
  kMinusEq,           // -=
  kStarEq,            // *=
  kSlashEq,           // /=
  kPercentEq,         // %=
  kAmpEq,             // &=
  kPipeEq,            // |=
  kCaretEq,           // ^=
  kLtLtEq,            // <<=
  kGtGtEq,            // >>=
  kLtLtLtEq,          // <<<=
  kGtGtGtEq,          // >>>=
  kQuestion,          // ?
  kColon,             // :
  kColonColon,        // ::
  kSemicolon,         // ;
  kComma,             // ,
  kDot,               // .
  kDotStar,           // .*
  kLParen,            // (
  kRParen,            // )
  kLBracket,          // [
  kRBracket,          // ]
  kLBrace,            // {
  kRBrace,            // }
  kHash,              // #
  kHashHash,          // ##
  kAt,                // @
  kAtAt,              // @@
  kArrow,             // ->
  kDashGtGt,          // ->>
  kEqGt,              // =>
  kStarGt,            // *>
  kAmpAmpAmp,         // &&&
  kPipeDashGt,        // |->
  kPipeEqGt,          // |=>
  kHashMinusHash,     // #-#
  kHashEqHash,        // #=#
  kApostrophe,        // '   (cast operator §6.24)
  kApostropheLBrace,  // '{  (assignment pattern prefix)
  kDollar,            // $   (queue dimension / last index)
  kPlusColon,         // +:  (indexed part-select up)
  kMinusColon,        // -:  (indexed part-select down)
  kAttrStart,         // (*  (attribute instance start)
  kAttrEnd,           // *)  (attribute instance end)

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

  // Remaining Annex B keywords (IEEE 1800-2023 Table B.1)
  kKwAcceptOn,
  kKwAlias,
  kKwAssert,
  kKwAssume,
  kKwBefore,
  kKwBind,
  kKwBins,
  kKwBinsof,
  kKwBuf,
  kKwBufif0,
  kKwBufif1,
  kKwCell,
  kKwChecker,
  kKwClocking,
  kKwCmos,
  kKwConfig,
  kKwConstraint,
  kKwContext,
  kKwCover,
  kKwCovergroup,
  kKwCoverpoint,
  kKwCross,
  kKwDefparam,
  kKwDesign,
  kKwDist,
  kKwEndchecker,
  kKwEndclass,
  kKwEndclocking,
  kKwEndconfig,
  kKwEndgroup,
  kKwEndprimitive,
  kKwEndproperty,
  kKwEndsequence,
  kKwEndspecify,
  kKwEndtable,
  kKwEvent,
  kKwEventually,
  kKwExpect,
  kKwExtern,
  kKwFirstMatch,
  kKwForeach,
  kKwForkjoin,
  kKwGlobal,
  kKwHighz0,
  kKwHighz1,
  kKwIff,
  kKwIfnone,
  kKwIgnoreBins,
  kKwIllegalBins,
  kKwImplements,
  kKwImplies,
  kKwIncdir,
  kKwInclude,
  kKwInside,
  kKwInstance,
  kKwInterconnect,
  kKwIntersect,
  kKwLarge,
  kKwLet,
  kKwLiblist,
  kKwLibrary,
  kKwLocal,
  kKwMacromodule,
  kKwMatches,
  kKwMedium,
  kKwModport,
  kKwNand,
  kKwNettype,
  kKwNexttime,
  kKwNmos,
  kKwNor,
  kKwNoshowcancelled,
  kKwNotif0,
  kKwNotif1,
  kKwPmos,
  kKwPrimitive,
  kKwProperty,
  kKwProtected,
  kKwPull0,
  kKwPull1,
  kKwPulldown,
  kKwPullup,
  kKwPulsestyleOndetect,
  kKwPulsestyleOnevent,
  kKwPure,
  kKwRand,
  kKwRandc,
  kKwRandcase,
  kKwRandsequence,
  kKwRcmos,
  kKwRejectOn,
  kKwRestrict,
  kKwRnmos,
  kKwRpmos,
  kKwRtran,
  kKwRtranif0,
  kKwRtranif1,
  kKwSAlways,
  kKwSEventually,
  kKwSNexttime,
  kKwSUntil,
  kKwSUntilWith,
  kKwScalared,
  kKwSequence,
  kKwShowcancelled,
  kKwSmall,
  kKwSoft,
  kKwSolve,
  kKwSpecify,
  kKwStrong,
  kKwStrong0,
  kKwStrong1,
  kKwSyncAcceptOn,
  kKwSyncRejectOn,
  kKwTable,
  kKwThroughout,
  kKwTimeprecision,
  kKwTimeunit,
  kKwTran,
  kKwTranif0,
  kKwTranif1,
  kKwType,
  kKwUntil,
  kKwUntilWith,
  kKwUntyped,
  kKwUse,
  kKwVectored,
  kKwVirtual,
  kKwWaitOrder,
  kKwWeak,
  kKwWeak0,
  kKwWeak1,
  kKwWildcard,
  kKwWith,
  kKwWithin,
  kKwXnor,
  kKwXor,
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
