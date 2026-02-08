#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "lexer/token.h"

namespace delta {

// Forward declarations
struct Expr;
struct Stmt;
struct ModuleItem;

// --- Expressions ---

enum class ExprKind : uint8_t {
  kIntegerLiteral,
  kRealLiteral,
  kTimeLiteral,
  kStringLiteral,
  kUnbasedUnsizedLiteral,
  kIdentifier,
  kSystemCall,
  kUnary,
  kBinary,
  kTernary,
  kConcatenation,
  kReplicate,
  kSelect,        // a[i] or a[i:j]
  kMemberAccess,  // a.b
  kCall,          // func(args)
};

struct Expr {
  ExprKind kind;
  SourceRange range;

  // Literal values
  std::string_view text;
  uint64_t int_val = 0;
  double real_val = 0.0;

  // Unary/binary
  TokenKind op = TokenKind::kEof;
  Expr* lhs = nullptr;
  Expr* rhs = nullptr;

  // Ternary
  Expr* condition = nullptr;
  Expr* true_expr = nullptr;
  Expr* false_expr = nullptr;

  // Call / system call
  std::string_view callee;
  std::vector<Expr*> args;

  // Select
  Expr* base = nullptr;
  Expr* index = nullptr;
  Expr* index_end = nullptr;

  // Concatenation / replicate
  std::vector<Expr*> elements;
  Expr* repeat_count = nullptr;
};

// --- Statements ---

enum class StmtKind : uint8_t {
  kBlock,
  kIf,
  kCase,
  kFor,
  kWhile,
  kForever,
  kRepeat,
  kDoWhile,
  kBreak,
  kContinue,
  kReturn,
  kBlockingAssign,
  kNonblockingAssign,
  kExprStmt,
  kTimingControl,
  kDelay,
  kEventControl,
  kWait,
  kFork,
  kDisable,
  kNull,
};

enum class Edge : uint8_t {
  kNone,
  kPosedge,
  kNegedge,
};

struct EventExpr {
  Edge edge = Edge::kNone;
  Expr* signal = nullptr;
};

struct CaseItem {
  std::vector<Expr*> patterns;
  Stmt* body = nullptr;
  bool is_default = false;
};

struct Stmt {
  StmtKind kind;
  SourceRange range;

  // Block
  std::vector<Stmt*> stmts;

  // If
  Expr* condition = nullptr;
  Stmt* then_branch = nullptr;
  Stmt* else_branch = nullptr;

  // Assign
  Expr* lhs = nullptr;
  Expr* rhs = nullptr;
  Expr* delay = nullptr;

  // For
  Stmt* for_init = nullptr;
  Expr* for_cond = nullptr;
  Stmt* for_step = nullptr;
  Stmt* for_body = nullptr;

  // Case
  std::vector<CaseItem> case_items;
  TokenKind case_kind = TokenKind::kKwCase;  // case/casex/casez

  // Timing
  std::vector<EventExpr> events;

  // Fork
  std::vector<Stmt*> fork_stmts;
  TokenKind join_kind = TokenKind::kKwJoin;

  // Expression statement
  Expr* expr = nullptr;

  // Repeat/while/do-while
  Stmt* body = nullptr;
};

// --- Declarations and module items ---

enum class Direction : uint8_t {
  kNone,
  kInput,
  kOutput,
  kInout,
  kRef,
};

enum class DataTypeKind : uint8_t {
  kImplicit,
  kLogic,
  kReg,
  kBit,
  kByte,
  kShortint,
  kInt,
  kLongint,
  kInteger,
  kReal,
  kShortreal,
  kTime,
  kRealtime,
  kString,
  kVoid,
  kNamed,
  kEnum,
  kStruct,
  kUnion,
};

struct EnumMember {
  std::string_view name;
  Expr* value = nullptr;
};

struct StructMember {
  DataTypeKind type_kind = DataTypeKind::kImplicit;
  bool is_signed = false;
  Expr* packed_dim_left = nullptr;
  Expr* packed_dim_right = nullptr;
  std::string_view name;
};

struct DataType {
  DataTypeKind kind = DataTypeKind::kImplicit;
  bool is_signed = false;
  bool is_packed = false;
  Expr* packed_dim_left = nullptr;
  Expr* packed_dim_right = nullptr;
  std::string_view type_name;
  std::vector<EnumMember> enum_members;
  std::vector<StructMember> struct_members;
};

struct PortDecl {
  Direction direction = Direction::kNone;
  DataType data_type;
  std::string_view name;
  Expr* default_value = nullptr;
  SourceLoc loc;
};

enum class ModuleItemKind : uint8_t {
  kNetDecl,
  kVarDecl,
  kParamDecl,
  kContAssign,
  kInitialBlock,
  kFinalBlock,
  kAlwaysBlock,
  kAlwaysCombBlock,
  kAlwaysFFBlock,
  kAlwaysLatchBlock,
  kGenerateFor,
  kGenerateIf,
  kModuleInst,
  kTypedef,
  kFunctionDecl,
  kTaskDecl,
  kImportDecl,
  kGateInst,
};

// clang-format off
enum class GateKind : uint8_t {
  // N-input gates
  kAnd, kNand, kOr, kNor, kXor, kXnor,
  // N-output gates
  kBuf, kNot,
  // Enable gates
  kBufif0, kBufif1, kNotif0, kNotif1,
  // Pass gates
  kTran, kRtran,
  // Pass enable gates
  kTranif0, kTranif1, kRtranif0, kRtranif1,
  // MOS switches
  kNmos, kPmos, kRnmos, kRpmos,
  // CMOS switches
  kCmos, kRcmos,
  // Pull gates
  kPullup, kPulldown,
};
// clang-format on

enum class AlwaysKind : uint8_t {
  kAlways,
  kAlwaysComb,
  kAlwaysFF,
  kAlwaysLatch,
};

struct ImportItem {
  std::string_view package_name;
  std::string_view item_name;
  bool is_wildcard = false;
};

struct FunctionArg {
  Direction direction = Direction::kNone;
  DataType data_type;
  std::string_view name;
};

struct ModuleItem {
  ModuleItemKind kind;
  SourceLoc loc;

  // Declarations
  DataType data_type;
  std::string_view name;
  Expr* init_expr = nullptr;
  std::vector<Expr*> unpacked_dims;

  // Continuous assignment
  Expr* assign_lhs = nullptr;
  Expr* assign_rhs = nullptr;

  // Always/initial/final blocks
  AlwaysKind always_kind = AlwaysKind::kAlways;
  Stmt* body = nullptr;
  std::vector<EventExpr> sensitivity;

  // Module instantiation
  std::string_view inst_module;
  std::string_view inst_name;
  std::vector<Expr*> inst_params;
  std::vector<std::pair<std::string_view, Expr*>> inst_ports;

  // Typedef
  DataType typedef_type;

  // Generate
  Stmt* gen_init = nullptr;
  Expr* gen_cond = nullptr;
  Stmt* gen_step = nullptr;
  std::vector<ModuleItem*> gen_body;
  ModuleItem* gen_else = nullptr;

  // Import
  ImportItem import_item;

  // Gate instantiation
  GateKind gate_kind = GateKind::kAnd;
  std::string_view gate_inst_name;
  std::vector<Expr*> gate_terminals;
  Expr* gate_delay = nullptr;

  // Function/task
  DataType return_type;
  std::vector<FunctionArg> func_args;
  std::vector<Stmt*> func_body_stmts;
};

// --- Top-level declarations ---

enum class ModuleDeclKind : uint8_t {
  kModule,
  kInterface,
  kProgram,
};

struct ModportPort {
  Direction direction = Direction::kNone;
  std::string_view name;
};

struct ModportDecl {
  std::string_view name;
  std::vector<ModportPort> ports;
  SourceLoc loc;
};

struct ModuleDecl {
  ModuleDeclKind decl_kind = ModuleDeclKind::kModule;
  std::string_view name;
  SourceRange range;
  std::vector<PortDecl> ports;
  std::vector<ModuleItem*> items;
  std::vector<std::pair<std::string_view, Expr*>> params;
  std::vector<ModportDecl*> modports;
};

struct PackageDecl {
  std::string_view name;
  SourceRange range;
  std::vector<ModuleItem*> items;
};

// --- Class declarations ---

enum class ClassMemberKind : uint8_t {
  kProperty,
  kMethod,
  kConstraint,
};

struct ClassMember {
  ClassMemberKind kind = ClassMemberKind::kProperty;
  SourceLoc loc;

  // Qualifiers
  bool is_static = false;
  bool is_virtual = false;
  bool is_local = false;
  bool is_protected = false;
  bool is_rand = false;
  bool is_randc = false;

  // Property fields
  DataType data_type;
  std::string_view name;
  Expr* init_expr = nullptr;

  // Method (reuses ModuleItem for function/task)
  ModuleItem* method = nullptr;
};

struct ClassDecl {
  std::string_view name;
  SourceRange range;
  bool is_virtual = false;
  std::string_view base_class;
  std::vector<ClassMember*> members;
  std::vector<std::pair<std::string_view, Expr*>> params;
};

struct CompilationUnit {
  std::vector<ModuleDecl*> modules;
  std::vector<PackageDecl*> packages;
  std::vector<ModuleDecl*> interfaces;
  std::vector<ModuleDecl*> programs;
  std::vector<ClassDecl*> classes;
};

}  // namespace delta
