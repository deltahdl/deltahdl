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
  kSelect,             // a[i] or a[i:j]
  kMemberAccess,       // a.b
  kCall,               // func(args)
  kAssignmentPattern,  // '{expr, ...}  (§5.10/§5.11)
  kCast,               // type'(expr)   (§6.24)
  kTypeRef,            // type(expr)    (§6.23)
  kPostfixUnary,       // a++, a--      (§11.4.2)
  kInside,             // expr inside { range_list }  (§11.4.13)
  kStreamingConcat,    // {<< [size] {exprs}} / {>> [size] {exprs}} (§11.4.14)
  kMinTypMax,          // expr : expr : expr  (§11.11)
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
  std::vector<std::string_view> arg_names;  // Named args (§13.5.4)

  // Select
  Expr* base = nullptr;
  Expr* index = nullptr;
  Expr* index_end = nullptr;
  bool is_part_select_plus = false;   // [base +: width] (§7.4.5)
  bool is_part_select_minus = false;  // [base -: width] (§7.4.5)

  // Array method with-clause (§7.12)
  Expr* with_expr = nullptr;

  // Concatenation / replicate / assignment pattern
  std::vector<Expr*> elements;
  Expr* repeat_count = nullptr;
  std::vector<std::string_view> pattern_keys;  // For named assignment patterns
};

// --- Attributes (§5.12) ---

struct Attribute {
  std::string_view name;
  Expr* value = nullptr;  // nullptr if no '= expr'
};

// --- Data types (must precede Stmt since Stmt uses DataType by value) ---

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
  kEvent,
  kChandle,
  kWire,              // Synthesizable net
  kTri,               // Tri-state net
  kWand,              // Wired-AND
  kWor,               // Wired-OR
  kTriand,            // Tri-state AND
  kTrior,             // Tri-state OR
  kTri0,              // Pull-down
  kTri1,              // Pull-up
  kTrireg,            // Capacitive storage
  kSupply0,           // Supply 0
  kSupply1,           // Supply 1
  kUwire,             // Unresolved wire
  kVirtualInterface,  // virtual interface (§25.9)
};

struct EnumMember {
  std::string_view name;
  Expr* value = nullptr;
  Expr* range_start = nullptr;  // For [N] or [N:M] syntax (§6.19.2)
  Expr* range_end = nullptr;    // For [N:M] syntax (nullptr for [N])
};

struct StructMember {
  DataTypeKind type_kind = DataTypeKind::kImplicit;
  bool is_signed = false;
  Expr* packed_dim_left = nullptr;
  Expr* packed_dim_right = nullptr;
  std::string_view name;
  Expr* init_expr = nullptr;         // Default member value (§7.2.2)
  std::vector<Expr*> unpacked_dims;  // Unpacked dims on member (§7.4)
};

struct DataType {
  DataTypeKind kind = DataTypeKind::kImplicit;
  bool is_signed = false;
  bool is_packed = false;
  bool is_const = false;
  bool is_net = false;       // True for wire/tri/wand/wor/supply/uwire types.
  bool is_tagged = false;    // union tagged (§7.3.2)
  bool is_soft = false;      // union soft (§7.3.1)
  bool is_vectored = false;  // vectored qualifier (§6.6.9)
  bool is_scalared = false;  // scalared qualifier (§6.6.9)
  Expr* packed_dim_left = nullptr;
  Expr* packed_dim_right = nullptr;
  std::string_view type_name;
  std::string_view scope_name;    // Package/class scope prefix (§6.25)
  std::string_view modport_name;  // virtual interface modport (§25.9)
  std::vector<EnumMember> enum_members;
  std::vector<StructMember> struct_members;
};

// --- Statements ---

enum class StmtKind : uint8_t {
  kBlock,
  kIf,
  kCase,
  kFor,
  kForeach,
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
  kWaitFork,  // wait fork (§9.6.1)
  kFork,
  kDisable,
  kDisableFork,  // disable fork (§9.6.3)
  kEventTrigger,
  kNull,
  kAssign,    // Procedural continuous assign (§10.6.1)
  kDeassign,  // Procedural deassign (§10.6.1)
  kForce,     // Force (§10.6.2)
  kRelease,   // Release (§10.6.2)
};

enum class Edge : uint8_t {
  kNone,
  kPosedge,
  kNegedge,
};

struct EventExpr {
  Edge edge = Edge::kNone;
  Expr* signal = nullptr;
  Expr* iff_condition = nullptr;  // §9.4.2 iff guard
};

struct CaseItem {
  std::vector<Expr*> patterns;
  Stmt* body = nullptr;
  bool is_default = false;
};

enum class CaseQualifier : uint8_t {
  kNone,
  kUnique,
  kUnique0,
  kPriority,
};

struct Stmt {
  StmtKind kind;
  SourceRange range;
  std::vector<Attribute> attrs;
  std::string_view label;
  CaseQualifier qualifier = CaseQualifier::kNone;

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
  DataType for_init_type;  // Non-implicit when for-init declares a variable

  // Case
  std::vector<CaseItem> case_items;
  TokenKind case_kind = TokenKind::kKwCase;  // case/casex/casez
  bool case_inside = false;  // case ... inside (LRM section 12.5.4)

  // Timing
  std::vector<EventExpr> events;
  bool is_star_event = false;  // @* or @(*) implicit sensitivity (§9.4.2.2)
  Expr* repeat_event_count = nullptr;  // repeat(N) @(event) (§9.4.5)

  // Fork
  std::vector<Stmt*> fork_stmts;
  TokenKind join_kind = TokenKind::kKwJoin;

  // Expression statement
  Expr* expr = nullptr;

  // Repeat/while/do-while
  Stmt* body = nullptr;

  // Foreach
  std::vector<std::string_view> foreach_vars;
};

// --- Declarations and module items ---

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
  kGenerateCase,
  kModuleInst,
  kTypedef,
  kFunctionDecl,
  kTaskDecl,
  kImportDecl,
  kExportDecl,
  kGateInst,
  kDefparam,
  kAlias,  // Net alias (§10.11)
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
  bool is_const = false;  // const ref (§13.5.2)
  DataType data_type;
  std::string_view name;
  Expr* default_value = nullptr;     // §13.5.3
  std::vector<Expr*> unpacked_dims;  // Unpacked array dims (§13.4)
};

struct ModuleItem;

struct GenerateCaseItem {
  std::vector<Expr*> patterns;
  bool is_default = false;
  std::vector<ModuleItem*> body;
};

struct ModuleItem {
  ModuleItemKind kind;
  SourceLoc loc;
  std::vector<Attribute> attrs;

  // Lifetime qualifiers (§6.21)
  bool is_automatic = false;
  bool is_static = false;

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
  bool inst_wildcard = false;        // .* port connection (§23.3.2.4)
  Expr* inst_range_left = nullptr;   // Instance array left bound (§23.3.2)
  Expr* inst_range_right = nullptr;  // Instance array right bound (§23.3.2)

  // Typedef
  DataType typedef_type;

  // Generate
  Stmt* gen_init = nullptr;
  Expr* gen_cond = nullptr;
  Stmt* gen_step = nullptr;
  std::vector<ModuleItem*> gen_body;
  ModuleItem* gen_else = nullptr;
  std::vector<GenerateCaseItem> gen_case_items;

  // Import
  ImportItem import_item;

  // Gate instantiation
  GateKind gate_kind = GateKind::kAnd;
  std::string_view gate_inst_name;
  std::vector<Expr*> gate_terminals;
  Expr* gate_delay = nullptr;

  // Gate drive strengths (§28.7)
  // 0=none, 1=highz, 2=weak, 3=pull, 4=strong, 5=supply
  uint8_t drive_strength0 = 0;
  uint8_t drive_strength1 = 0;

  // Function/task
  DataType return_type;
  std::vector<FunctionArg> func_args;
  std::vector<Stmt*> func_body_stmts;

  // Defparam: list of (hierarchical_path_expr, value_expr) pairs
  std::vector<std::pair<Expr*, Expr*>> defparam_assigns;

  // Net alias (§10.11)
  std::vector<Expr*> alias_nets;
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
  Expr* expr = nullptr;    // Port expression: .name(expr) (§25.5.4)
  bool is_import = false;  // import task/function (§25.7)
  bool is_export = false;  // export task/function (§25.7)
};

struct ModportDecl {
  std::string_view name;
  std::vector<ModportPort> ports;
  SourceLoc loc;
};

struct ModuleDecl {
  ModuleDeclKind decl_kind = ModuleDeclKind::kModule;
  bool is_extern = false;  // extern module declaration (§23.2.1)
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

// --- User-Defined Primitives (§29) ---

struct UdpTableRow {
  std::vector<char> inputs;  // '0','1','x','?','b','r','f','p','n','*'
  char current_state = 0;    // For sequential UDPs (0 if combinational)
  char output = '0';         // '0','1','x','-'
};

struct UdpDecl {
  std::string_view name;
  SourceRange range;
  std::string_view output_name;
  std::vector<std::string_view> input_names;
  bool is_sequential = false;
  std::vector<UdpTableRow> table;
};

struct CompilationUnit {
  std::vector<ModuleDecl*> modules;
  std::vector<PackageDecl*> packages;
  std::vector<ModuleDecl*> interfaces;
  std::vector<ModuleDecl*> programs;
  std::vector<ClassDecl*> classes;
  std::vector<UdpDecl*> udps;
};

}  // namespace delta
