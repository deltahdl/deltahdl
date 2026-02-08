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
  IntegerLiteral,
  RealLiteral,
  StringLiteral,
  UnbasedUnsizedLiteral,
  Identifier,
  SystemCall,
  Unary,
  Binary,
  Ternary,
  Concatenation,
  Replicate,
  Select,        // a[i] or a[i:j]
  MemberAccess,  // a.b
  Call,          // func(args)
};

struct Expr {
  ExprKind kind;
  SourceRange range;

  // Literal values
  std::string_view text;
  uint64_t int_val = 0;

  // Unary/binary
  TokenKind op = TokenKind::Eof;
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
  Block,
  If,
  Case,
  For,
  While,
  Forever,
  Repeat,
  DoWhile,
  Break,
  Continue,
  Return,
  BlockingAssign,
  NonblockingAssign,
  ExprStmt,
  TimingControl,
  Delay,
  EventControl,
  Wait,
  Fork,
  Disable,
  Null,
};

enum class Edge : uint8_t {
  None,
  Posedge,
  Negedge,
};

struct EventExpr {
  Edge edge = Edge::None;
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
  TokenKind case_kind = TokenKind::KwCase;  // case/casex/casez

  // Timing
  std::vector<EventExpr> events;

  // Fork
  std::vector<Stmt*> fork_stmts;
  TokenKind join_kind = TokenKind::KwJoin;

  // Expression statement
  Expr* expr = nullptr;

  // Repeat/while/do-while
  Stmt* body = nullptr;
};

// --- Declarations and module items ---

enum class Direction : uint8_t {
  None,
  Input,
  Output,
  Inout,
  Ref,
};

enum class DataTypeKind : uint8_t {
  Implicit,
  Logic,
  Reg,
  Bit,
  Byte,
  Shortint,
  Int,
  Longint,
  Integer,
  Real,
  Shortreal,
  Time,
  Realtime,
  String,
  Void,
  Named,
};

struct DataType {
  DataTypeKind kind = DataTypeKind::Implicit;
  bool is_signed = false;
  Expr* packed_dim_left = nullptr;
  Expr* packed_dim_right = nullptr;
  std::string_view type_name;
};

struct PortDecl {
  Direction direction = Direction::None;
  DataType data_type;
  std::string_view name;
  Expr* default_value = nullptr;
  SourceLoc loc;
};

enum class ModuleItemKind : uint8_t {
  NetDecl,
  VarDecl,
  ParamDecl,
  ContAssign,
  InitialBlock,
  FinalBlock,
  AlwaysBlock,
  AlwaysCombBlock,
  AlwaysFFBlock,
  AlwaysLatchBlock,
  GenerateBlock,
  ModuleInst,
};

enum class AlwaysKind : uint8_t {
  Always,
  AlwaysComb,
  AlwaysFF,
  AlwaysLatch,
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
  AlwaysKind always_kind = AlwaysKind::Always;
  Stmt* body = nullptr;
  std::vector<EventExpr> sensitivity;

  // Module instantiation
  std::string_view inst_module;
  std::string_view inst_name;
  std::vector<Expr*> inst_params;
  std::vector<std::pair<std::string_view, Expr*>> inst_ports;
};

// --- Top-level declarations ---

struct ModuleDecl {
  std::string_view name;
  SourceRange range;
  std::vector<PortDecl> ports;
  std::vector<ModuleItem*> items;
  std::vector<std::pair<std::string_view, Expr*>> params;
};

struct CompilationUnit {
  std::vector<ModuleDecl*> modules;
};

}  // namespace delta
