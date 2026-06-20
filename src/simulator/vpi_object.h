#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/vpi_constants.h"

namespace delta {

struct VpiObject {
  int type = 0;
  std::string_view name;
  std::string full_name;
  Variable* var = nullptr;
  Net* net = nullptr;
  VpiObject* parent = nullptr;
  int direction = 0;
  int size = 0;
  int index = 0;

  // §37.36 detail 2: the primitive type a UDP reports through
  // vpi_get(vpiPrimType)
  // - vpiSeqPrim for a sequential UDP, vpiCombPrim for a combinational one. The
  // same property labels a primitive in §37.35; both read it from here. Zero
  // when the object reports no primitive type.
  int prim_type = 0;

  // §6.9.2: the advisory accessibility keyword a vector net was declared with.
  // At most one is set. They drive how the PLI reports the net's expansion
  // through vpi_get(vpiExplicitScalared/vpiExplicitVectored/vpiExpanded): a
  // scalared net is always reported expanded; a vectored net is reported
  // unexpanded.
  bool is_vectored = false;
  bool is_scalared = false;

  // §37.3.7: declared lifetime. False means the object is static; true means it
  // is non-static (an automatic variable or a dynamic object). Static is the
  // default.
  bool automatic = false;

  // §37.3.7: how this object's storage was obtained. Defaulting to
  // kVpiOtherScheme directly encodes the rule that every object not allocated
  // with a frame/thread or in dynamic memory reports vpiOtherScheme.
  int alloc_scheme = kVpiOtherScheme;

  // §37.3.6: whether this object represents protected code (sealed in a
  // decryption envelope). Reported by the vpiIsProtected property. Unless
  // otherwise specified, accessing a protected object's properties is an error;
  // vpiType and vpiIsProtected are the permitted exceptions.
  bool is_protected = false;

  // §38.12: whether this callback object stands in for a user-defined system
  // task or system function. When true, `index` selects the registration
  // record vpi_get_systf_info() reports; this separates a system task/function
  // callback from a simulation callback, which is also a vpiCallback object.
  bool is_systf = false;

  // §38.33: the implementation storage location vpi_put_userdata() writes for a
  // system task or system function call instance. vpi_put_userdata() associates
  // this user-data value with the call handle so a later vpi_get_userdata() can
  // read it back. It is null until set, and is cleared on a simulation restart
  // or reset (after either, a fresh vpi_get_userdata() yields null until the
  // application sets it again).
  void* user_data = nullptr;

  // §38.34: whether a vpiSchedEvent handle still names an event sitting in the
  // event queue. vpi_put_value() with vpiReturnEvent hands back such a handle
  // marked scheduled; vpi_get(vpiScheduled) reports this flag, and
  // vpi_put_value() with vpiCancelEvent clears it when the event is removed.
  bool scheduled = false;

  // §37.10 detail 6: items that vpi_handle_by_name() must not be able to reach.
  // An imported item is brought into scope by an import declaration; a
  // compilation-unit object lives directly in the $unit compilation-unit scope.
  bool imported = false;
  bool in_compilation_unit = false;

  // §37.16 detail 9: whether a net was created by implicit declaration (a net
  // referenced without an explicit declaration). Reported by vpiImplicitDecl;
  // an implicit net's vpiLineNo is 0 and its vpiFile names where the net was
  // first referenced (carried in `file`).
  bool implicit_decl = false;

  // §37.10 detail 7: the time precision an instance was elaborated with. Only
  // meaningful on module objects; the design-wide query reads it across every
  // module to find the smallest precision.
  int time_precision = 0;

  // §38.13: the object's time unit, as a base-ten exponent of one second (e.g.
  // -9 for 1 ns, -12 for 1 ps). vpi_get_time() scales a scaled-real result to
  // this unit - the "timescale of the object". Zero leaves the scaled value
  // expressed in the simulation time unit (no scaling).
  int time_unit = 0;

  // §37.81: for a time queue object produced by the vpi_iterate(vpiTimeQueue,
  // NULL) walk, the simulation time (in ticks of the simulation time unit) of
  // the time slot it represents. The iteration hands the objects back in
  // increasing order of this value (detail 1). Zero for any other object.
  uint64_t time_queue_time = 0;

  std::string library_name;
  std::string cell_name;
  std::string config_name;

  // §37.30 detail 1: the definition name an interface typespec reports through
  // vpi_get_str(vpiDefName) - the modport identifier when the typespec
  // represents a modport, the interface declaration's identifier when it
  // represents an interface. Distinct from `name`, which carries the typespec's
  // vpiName (the typedef name); empty when unset.
  std::string def_name;

  // §37.54 (D2): the operation type an operation object reports through
  // vpi_get(vpiOpType). For a sequence expression's operation this is one of
  // the sequence operators (see VpiIsSequenceExprOpType); zero when unset.
  int op_type = 0;

  // §37.59: the constant type a constant object reports through
  // vpi_get(vpiConstType). vpiUnboundedConst names the $ value used in
  // assertion ranges (detail 4). Zero when unset.
  int const_type = 0;

  // §37.59: the index-part-select type an indexed part-select reports through
  // vpi_get(vpiIndexedPartSelectType) - whether the selection ascends (+:) or
  // descends (-:). Zero when unset.
  int indexed_part_select_type = 0;

  // §37.52 detail 3: whether an operation reports the strong version of its
  // operator through vpi_get(vpiOpStrong). Meaningful only for the operators
  // VpiIsOpStrongValidOp accepts (and for sequence expressions); false
  // otherwise.
  bool op_strong = false;

  // §37.50: whether a cover covers a sequence rather than a property, reported
  // through vpi_get(vpiIsCoverSequence). Meaningful only for a cover; false
  // otherwise.
  bool cover_sequence = false;

  // §37.50 (detail 1): whether the concurrent assertion's clocking event was
  // inferred from context rather than written explicitly, reported through
  // vpi_get(vpiIsClockInferred). The event reached through vpiClockingEvent is
  // the actual event either way; this flag only records which form produced it.
  bool clock_inferred = false;

  // §37.55: whether an immediate assertion (immediate assert/assume/cover) is a
  // deferred assertion and whether it is a final assertion, reported through
  // vpi_get(vpiIsDeferred) and vpi_get(vpiIsFinal). Both are Boolean properties
  // drawn only on the immediate-assertion kinds; false by default.
  bool is_deferred = false;
  bool is_final = false;

  // §37.43/§37.44: whether a frame or a thread is the active one, reported
  // through vpi_get(vpiActive). The object that currently holds execution is
  // active; an inactive one is suspended or otherwise not running. There is at
  // most one active frame at a time in a given thread (§37.43 detail 4). False
  // by default.
  bool active = false;

  // §37.49: the source span an assertion object occupies. start/column/end are
  // reported through vpi_get(vpiStartLine/vpiColumn/vpiEndLine/vpiEndColumn)
  // and the file through vpi_get_str(vpiFile); the assertion name reuses
  // `name`.
  std::string file;
  int start_line = 0;
  int column = 0;
  int end_line = 0;
  int end_column = 0;

  // §37.3.3: the source line this object occupies, reported through
  // vpi_get(vpiLineNo). One of the two location properties (with vpiFile, held
  // in `file`) that every object mapping to source text carries; both are
  // omitted for the object kinds §37.3.3 lists as exceptions. May be shifted by
  // the `line directive (§22.12).
  int line_no = 0;

  // §37.83: the scalar properties the Attribute data model diagram draws on an
  // attribute object (vpiAttribute). vpiDefAttribute reports whether the
  // attribute was specified on a definition (such as a UDP or module
  // definition) rather than on an instance; vpiDefFile and vpiDefLineNo give
  // the source file and line of that definition. The attribute's vpiName reuses
  // `name`, its value is reached through vpi_get_value() (§38.34), and its
  // owning object is reached through vpiParent (reusing `parent`). All default
  // to the "unset" state.
  bool def_attribute = false;
  std::string def_file;
  int def_line_no = 0;

  // §38.10: the delays this object carries, in the order they occur in the
  // SystemVerilog description. vpi_get_delays() reports them in this order, so
  // da[0] is the first source delay, da[1] the second, and so on. Empty for an
  // object that bears no delays.
  std::vector<VpiDelayInfo> delays;

  // §37.3.4: the source-specified delay expression this object exposes through
  // the vpiDelay relation. A net, primitive, module path, timing check, or
  // continuous assignment can carry a delay written in the SystemVerilog
  // source; vpiDelay reaches the expression standing for it - a single
  // constant-valued expression when one delay is written, or a vpiListOp
  // operation listing them when more than one is written. NULL when the object
  // carries no source delay. Distinct from `delays` above, which holds the
  // actual delay values the tool uses (reported by vpi_get_delays(), §38.10),
  // not the source expression.
  VpiObject* delay_expr = nullptr;

  // §37.14 / §37.15: a port (or a ref obj) carries two designated connections.
  // vpiHighConn reaches the hierarchically higher connection (closer to the top
  // module); vpiLowConn reaches the lower one. A null pointer is the natural
  // encoding of "no such connection", which §37.14 detail 10 mandates as NULL
  // for a null port (lowConn) or an unconnected instance (highConn).
  VpiObject* high_conn = nullptr;
  VpiObject* low_conn = nullptr;

  // §37.15 detail 3: the actual instantiated object a ref obj is bound to,
  // reported through the vpiActual relation. NULL when the ref obj is not bound
  // to an actual at the time of the query.
  VpiObject* actual = nullptr;

  // §37.61 detail 1: the dynamic prefix this object is reached through - the
  // class var, virtual interface var, or clocking block that prefixes the
  // expression, named event, or named event array in the source. Reported
  // through the vpiPrefix relation; NULL when the object is not so prefixed. A
  // tf call's prefix is modeled separately by §37.42.
  VpiObject* prefix = nullptr;

  // §37.61 detail 3: how this object's correspondence to an actual is fixed
  // (one of the kVpiActual* provenances). The default, kVpiActualBySimTime,
  // leaves vpiHasActual driven by whether `actual` is bound at the current
  // simulation time; the other values pin the answer per the object's
  // provenance.
  int actual_origin = kVpiActualBySimTime;

  // §37.14 detail 1: a port's type, one of vpiPort, vpiInterfacePort, or
  // vpiModportPort, reported through vpi_get(vpiPortType). It is derived from
  // the formal, not the actual. Zero when unset.
  int port_type = 0;

  // §37.14 detail 8: whether a port was given an explicit name in the port
  // list, reported through vpi_get(vpiExplicitName).
  bool explicit_name = false;

  // §37.14 detail 10/11: whether a port is a null port (e.g. "module M();").
  // Its vpiLowConn is NULL and its vpiSize is 0.
  bool null_port = false;

  // §37.15 detail 5: whether a ref obj refers to a generic interface. Only
  // meaningful when the ref obj refers to an interface; reported through
  // vpi_get(vpiGeneric).
  bool generic_interface = false;

  // §37.30: whether an interface typespec represents a modport rather than an
  // interface, reported through vpi_get(vpiIsModPort). It also selects how
  // vpiDefName and vpiParent are interpreted (details 1 and 2). False (an
  // interface, not a modport) by default.
  bool is_modport = false;

  // §37.72: the case kind a case statement reports through vpi_get(vpiCaseType)
  // - one of vpiCaseExact, vpiCaseX, or vpiCaseZ. Zero when unset.
  int case_type = 0;

  // §37.72: the qualifier flags a case statement reports through
  // vpi_get(vpiQualifier) - a bitwise OR of the unique/priority/etc. qualifier
  // bits (vpiNoQualifier when the statement carries no qualifier).
  int qualifier = 0;

  // §37.72 detail 2: whether a case item is the default item. The default case
  // item carries no condition expression, so iterating its match expressions
  // (vpi_iterate(vpiExpr, item)) returns NULL and it groups no conditions.
  bool default_case_item = false;

  // §37.63 detail 1: the always kind a process reports through
  // vpi_get(vpiAlwaysType) - one of vpiAlways, vpiAlwaysComb, vpiAlwaysFF, or
  // vpiAlwaysLatch. A process that is not an always procedure (an initial or
  // final process), or an always_type left unset, carries none of those and so
  // has no always type to report. Zero (no always type) by default.
  int always_type = 0;

  // §37.62: whether an event statement is a blocking event trigger (->) rather
  // than a nonblocking one (->>), reported through vpi_get(vpiBlocking). The
  // property is drawn only on the event statement object. False by default.
  bool blocking = false;

  // §37.12 detail 6: the join kind that terminates a fork-join block, reported
  // through vpi_get(vpiJoinType) - one of vpiJoin, vpiJoinNone, or vpiJoinAny.
  // vpiJoin (zero) by default.
  int join_type = 0;

  // §37.12 detail 2: whether a for statement declares its loop control
  // variables local to the loop, reported through vpi_get(vpiLocalVarDecls). A
  // for statement is a scope if and only if this is true. False by default.
  bool local_var_decls = false;

  // §37.12 detail 4: whether an object was imported into its enclosing scope
  // through an import declaration and is actually referenced there. A scope's
  // vpiImport iteration returns exactly the children carrying this mark, so an
  // item merely made visible by an import (but not referenced) is not flagged.
  // False by default.
  bool imported = false;

  // §37.35 detail 4 / §37.9 detail 1: whether an object is an element within an
  // array. It gates the vpiIndex transition for both an array-member primitive
  // and a program that is an element of an instance array: such an object
  // reaches the index expression that selects it within the array through that
  // transition, while an object that is not an array element returns NULL
  // there.
  bool array_member = false;

  // §37.35 detail 4 / §37.9 detail 1: for an array-member object, the index
  // expression the vpiIndex transition reaches - the expr that locates it
  // within its array. The target's own type is an expr kind (not vpiIndex), so
  // it is held as a designated pointer rather than found by the generic child
  // walk.
  VpiObject* index_expr = nullptr;

  // §37.17 detail 21 / §38.35: the array kind this object reports through
  // vpi_get(vpiArrayType) - vpiStaticArray, vpiDynamicArray, vpiAssocArray, or
  // vpiQueueArray. vpi_put_value_array() writes only into a static unpacked
  // array, so it reads this to confirm the target is a vpiStaticArray before
  // touching any element. Zero when the object is not an array.
  int array_type = 0;

  // §38.35: for a static unpacked array, the declared index values of each
  // unpacked dimension in left-to-right (declaration) order - so a[2:0][3:5]
  // holds {{2,1,0},{3,4,5}}. The size of this list is the number of unpacked
  // dimensions, which the index_p argument must match; the lists map an index
  // coordinate to the element's flat ordinal (rightmost dimension varying
  // fastest), which is the order vpi_put_value_array() fills elements in. The
  // element children carry that flat ordinal in their `index` field.
  std::vector<std::vector<int>> array_dim_indices;

  // §37.5 detail 1: whether a module is a top-level module - one with no
  // instantiating parent. The top-level modules are exactly the ones reached by
  // iterating vpiModule with a NULL reference object; a module nested inside
  // another scope is reached through its parent instead and so is excluded from
  // that iteration. Also reported directly through vpi_get(vpiTopModule). False
  // by default.
  bool top_module = false;

  // §37.5: the default net decay time a module reports through
  // vpi_get(vpiDefDecayTime) - the number of time units a tri-state net holds
  // its last driven value before decaying to x. Zero when unset.
  int def_decay_time = 0;

  // §37.42 detail 2: for a method func/task call, the object the method is
  // applied to, reached through vpiPrefix. For the call "packet.send()" this is
  // the class variable "packet". Null for a tf call that is not a method call,
  // where the vpiPrefix relation does not apply.
  VpiObject* tf_prefix = nullptr;

  // §37.42 detail 1: the with-clause a method call carries (an expression, or a
  // constraint for randomize), reached through vpiWith. The relation is
  // available only for the methods that accept a with clause - the randomize
  // methods (18.7) and the array locator methods (7.12.1); `tf_with_method`
  // records whether this call is one of those. vpiWith reports `tf_with` only
  // when it is, NULL otherwise.
  VpiObject* tf_with = nullptr;
  bool tf_with_method = false;

  // §37.42 detail 11: whether a method call invokes a built-in method (one
  // SystemVerilog provides) rather than a user-written class method. A built-in
  // method func call has no user function object, so vpiFunction reports NULL;
  // likewise a built-in method task call reports NULL for vpiTask.
  bool builtin_method = false;

  // §37.47 detail 3: the bit offset a cont assign bit reports through
  // vpi_get(vpiOffset). The offset is measured from the least significant bit,
  // so the LSB carries offset zero and the bit n positions above it carries
  // offset n. Zero by default, which is the value the LSB must report.
  int offset = 0;

  // §37.47: whether a continuous assignment is a net declaration assignment
  // (the assignment written as part of a net declaration, as in "wire w = a &
  // b;") rather than a standalone assign statement. Reported through the
  // vpiNetDeclAssign Boolean property; false by default.
  bool net_decl_assign = false;

  // §37.47: the drive strengths a continuous assignment carries on its 0 and 1
  // values, reported through vpi_get(vpiStrength0) and vpi_get(vpiStrength1).
  // Zero when unset.
  int strength0 = 0;
  int strength1 = 0;

  // §37.34: a constraint's access type, reported through
  // vpi_get(vpiAccessType). For a constraint the only values are vpiExternAcc -
  // when the constraint is declared outside its enclosing class declaration
  // (detail 3) - and zero.
  int access_type = 0;

  // §37.34: whether a constraint is virtual, reported through the vpiVirtual
  // Boolean property; false by default.
  bool is_virtual = false;

  // §37.34: whether a constraint is currently enabled (constraint_mode),
  // reported through the vpiIsConstraintEnabled Boolean property.
  bool constraint_enabled = false;

  // §37.34: the distribution kind a dist item carries (e.g. vpiEqualDist or
  // vpiDivDist), reported through vpi_get(vpiDistType) as an int property.
  int dist_type = 0;

  // §37.26: the Boolean figure properties a struct/union object carries.
  // `packed` backs vpiPacked - whether the structure or union is packed; a
  // packed aggregate has a single vector value while an unpacked one does not.
  // `tagged` backs vpiTagged - whether the union is a tagged union. `soft`
  // backs vpiSoft - whether the (packed) union is a soft-packed union. All
  // three default false, so any object that is not so declared reports FALSE.
  bool packed = false;
  bool tagged = false;
  bool soft = false;

  // §37.28: the parameter / param assign figure properties and designated
  // relation targets that the generic child-by-type walk cannot serve.
  // `local_param` backs the parameter's vpiLocalParam Boolean (whether it is a
  // localparam). `conn_by_name` backs a param assign's vpiConnByName Boolean
  // (whether the override connects by name). `param_default` is the vpiExpr
  // target - a value parameter's default value expression or a type parameter's
  // default typespec (detail 3). `param_typespec` is a type parameter's
  // vpiTypespec target - the typespec it resolved to at the end of elaboration,
  // kept without typedef-alias resolution (detail 2). `explicit_param_range`
  // records whether a value parameter was declared with an explicit range; when
  // false, vpiLeftRange and vpiRightRange both report a null handle (detail 5).
  // `param_left_range` and `param_right_range` hold the range-bound expressions
  // for a parameter that does have an explicit range.
  bool local_param = false;
  bool conn_by_name = false;
  VpiObject* param_default = nullptr;
  VpiObject* param_typespec = nullptr;
  bool explicit_param_range = false;
  VpiObject* param_left_range = nullptr;
  VpiObject* param_right_range = nullptr;

  // §37.31 detail 1: whether a class method is an implicit built-in method -
  // one SystemVerilog provides for which the class carries no explicit
  // declaration. The vpiMethods iteration of a class defn omits such methods
  // (it returns only explicitly declared static and automatic methods); false
  // by default, so an ordinary declared method is always reported.
  bool implicit_builtin_method = false;

  // §37.31 detail 3: whether a constraint is an inline constraint (one written
  // at a randomize()-with call site, 18.7) rather than a normal constraint
  // declared as a class item. A class defn's vpiConstraint iteration returns
  // only normal constraints, so an inline constraint is skipped; false by
  // default.
  bool inline_constraint = false;

  // §37.33 detail 1: a class object's identifier, reported through
  // vpi_get(vpiObjId). It is a 64-bit value guaranteed unique among all live
  // dynamic objects that carry this property for as long as the object lives;
  // once the object is reclaimed its value may be reused. §37.33 detail 2: a
  // class variable does not store its own identifier - it reports the
  // identifier of the object it currently references (see referenced_object),
  // or 0 when it references none. Zero by default.
  int64_t obj_id = 0;

  // §37.33 detail 2/5: the class object a class variable currently references.
  // A class variable holding the value null references no object, in which case
  // this is null: its vpiObjId is then 0 (detail 2) and the vpiClassObj
  // relation applied to it reaches a null handle (detail 5). Null by default.
  VpiObject* referenced_object = nullptr;

  // §37.40 detail 1: the event terms a timing check reaches through its
  // vpiTchkRefTerm and vpiTchkDataTerm relations. The reference term is the
  // check's reference event or controlled reference event; the data term is its
  // data event, present only when the check has one (otherwise null). Both are
  // tchk term objects, whose own type (vpiTchkTerm) differs from the relation
  // enum, so they are held as designated pointers rather than found by a type
  // match. Null by default.
  VpiObject* tchk_ref_term = nullptr;
  VpiObject* tchk_data_term = nullptr;

  // §37.45: the two delay terminals a delay device reaches. vpiInTerm denotes
  // the input delay term and vpiOutTerm the output delay term. Each is a delay
  // term object, whose own type (vpiDelayTerm) differs from the relation enum
  // (vpiInTerm / vpiOutTerm), so - as with the timing-check terms above - they
  // are held as designated pointers rather than found by a type match. Null by
  // default.
  VpiObject* in_term = nullptr;
  VpiObject* out_term = nullptr;

  // §37.79: the left- and right-hand side expressions of a procedural
  // continuous assignment family object - an assign statement, a force, a
  // deassign, or a release. The diagram draws vpiLhs from all four and vpiRhs
  // only from the assign statement and force (deassign and release name a
  // target but supply no value). Each side is an expression, whose own type is
  // an expression kind rather than the vpiLhs / vpiRhs relation enum, so - as
  // with the other designated targets above - they are held as designated
  // pointers rather than found by a type match. Null by default.
  VpiObject* lhs = nullptr;
  VpiObject* rhs = nullptr;

  // §37.45: the vpiDelayType integer property carried by a delay device and by
  // a delay term. It names the kind of delay (for example a module-path or
  // timing delay). Zero by default, which is what every object that is not a
  // delay device or delay term reports.
  int delay_type = 0;

  // §37.38 detail 1 / §37.75 detail 1: the variable a foreach constraint or
  // foreach statement indexes. The foreach reaches it through the vpiVariables
  // relation, where it represents the array (or string) being iterated over.
  // Its own type is a variable kind, not the relation enum, so it is held as a
  // designated pointer rather than found by a type match. Null by default -
  // only a foreach constraint or foreach statement carries one.
  VpiObject* foreach_array = nullptr;

  // §37.38 detail 2 / §37.75 detail 2: the index variables of a foreach
  // constraint or foreach statement, in left-to-right declaration order, as
  // walked by the vpiLoopVars iteration. A null entry marks an index position
  // that was skipped in the foreach header; the iteration represents such a
  // position with a freshly built vpiOperation whose operator is the null
  // operation, so callers see a placeholder in that slot. Empty for any object
  // that is neither a foreach constraint nor a foreach statement.
  std::vector<VpiObject*> loop_vars;

  // §37.38 detail 3: the constraint expressions held in the body of a
  // constraint-expression container - an implication, a constraint if, a
  // constraint if-else, or a foreach constraint - in the order they occur. The
  // vpiConstraintExpr iteration walks this list so the expressions come back in
  // source order. Empty for an object that holds no such body.
  std::vector<VpiObject*> constraint_exprs;

  // §37.41 details 1-3: the variable that captures a function's return value,
  // reached through the vpiReturn relation. Detail 1 makes a function contain a
  // return-capture object sharing the function's name, size, and type; detail 2
  // makes vpi_handle(vpiReturn, function) hand back that variable so a caller
  // can inspect a user-defined return type through it; detail 3 makes the
  // relation always reach a var object, even for a simple scalar return. Its
  // own type is a variable kind, not the relation enum, so it is held as a
  // designated pointer rather than found by the generic child walk. Null for a
  // task (which returns nothing) and for any object that is not a function.
  VpiObject* return_var = nullptr;

  // §37.41 details 6-10: the DPI properties a DPI import/export task or
  // function reports. `is_dpi` marks the tf as a DPI import or export, and
  // `dpi_export` distinguishes an export (true) from an import (false);
  // vpiAccessType reports vpiDPIExportAcc or vpiDPIImportAcc from the pair
  // (detail 6). `dpi_pure` backs vpiDPIPure - true only for a pure DPI import
  // function (detail 7). `dpi_context` backs vpiDPIContext - true for a context
  // import (detail 8). `is_dpi_c` selects the flavor vpiDPICStr reports:
  // vpiDPIC for a "DPI-C" tf, vpiDPI for a "DPI" tf (detail 9).
  // `dpi_c_identifier` is the C linkage name vpiDPICIdentifier reports (detail
  // 10). All default to the not-a-DPI-tf values, so a plain task or function
  // reports none of them.
  bool is_dpi = false;
  bool dpi_export = false;
  bool dpi_pure = false;
  bool dpi_context = false;
  bool is_dpi_c = false;
  std::string dpi_c_identifier;

  std::vector<VpiObject*> children;
  size_t scan_index = 0;

  // §38.23: for an iterator object (type vpiIterator), the reference object the
  // iteration was created over. It is reported back through the vpiUse
  // relation, so vpi_handle(vpiUse, iterator) recovers the object the iterator
  // walks.
  VpiObject* iter_ref = nullptr;

  // §37.84: for an iterator object (type vpiIterator), the kind of object the
  // iteration walks - the type code handed to vpi_iterate when the iterator was
  // created. It is reported back through the iterator's vpiIteratorType
  // property, so vpi_get(vpiIteratorType, iterator) recovers what the iterator
  // traverses.
  int iter_type = 0;

  // §38.3: the underlying simulation object this handle denotes, when that is
  // not the handle object itself. Two distinct handles can name one and the
  // same object - e.g. a packed-struct bit reachable both as ps[0] and as
  // ps.b[7], or an expression i[j] that resolves to the array element i[0].
  // vpi_compare_objects() follows this link to a common representative, so it
  // reports such handles equal even though a C "==" of the handle pointers
  // would not. Null means the handle is its own representative.
  VpiObject* same_object_as = nullptr;

  // §38.3: whether the underlying simulation object this handle denotes exists
  // at the time it is queried. vpi_compare_objects() compares objects only
  // "provided that the simulation object exists", so a handle whose object is
  // absent (for instance a class handle that is still null) never compares
  // equal. True by default - most objects exist for the whole simulation.
  bool object_exists = true;

  // §37.2.2: whether this particular handle has been released. A released
  // handle is no longer a live handle to its object, but the underlying object
  // is unaffected - a distinct, unreleased handle to the same object keeps
  // working. The flag is per-handle, so releasing one handle leaves any other
  // handle to the same object untouched. False until vpi_release_handle() (or a
  // simulation event that frees the handle's object) releases it.
  bool released = false;

  // §37.3.5: whether this expression has side effects when it is evaluated. The
  // subclause classifies such expressions as ones built from assignment
  // operators, increment or decrement operators, function or system-function
  // calls (including built-in methods) that change simulation state by some
  // means other than their return value, or any expression that contains such
  // an expression as an operand, argument, or index. This flag marks an
  // already-classified expression; the VPI value, property, and relation
  // routines consult it. False by default.
  bool has_side_effects = false;

  // §37.3.5: a running count of how many times this expression has been
  // evaluated through VPI. Applying vpi_get_value() to an expression with side
  // effects shall fully evaluate it together with its side effects, so that
  // read bumps this counter - the observable stand-in for the state change the
  // evaluation performs (for instance an embedded i++). Zero until the first
  // such evaluation.
  int side_effect_count = 0;

  // §37.3.5: whether a VPI query for a property or relation of this expression
  // cannot be answered without also evaluating an expression that has side
  // effects. When set, vpi_get() and vpi_handle() refuse the query and record
  // an error rather than silently triggering the side effect - for example
  // asking the vpiSize of a function call whose size cannot be known without
  // calling it. False by default; most queries are answerable structurally.
  bool property_needs_side_effect_eval = false;

  // §37.3.5: the index expressions that select into this object, in order. It
  // is an error to apply vpi_put_value() to an object when any of these index
  // expressions has side effects (for instance my_array[i++]); vpi_put_value()
  // consults this list and refuses the write in that case. Empty for an object
  // that is not an indexed select.
  std::vector<VpiObject*> index_expressions;

  // §37.23 detail 2: for a nettype declaration (type vpiNetTypedef) that is an
  // alias of another nettype declaration, the aliased nettype it stands for.
  // Reached through vpiNetTypedefAlias, which must report a non-null handle to
  // that nettype. Null for a nettype that is not an alias.
  VpiObject* nettype_alias = nullptr;

  // §37.23 detail 1: for a nettype declaration (type vpiNetTypedef), the
  // resolution function associated with it, reached through vpiWith. A nettype
  // declared without an associated resolution function has none, so this stays
  // null and vpiWith reports NULL.
  VpiObject* nettype_with = nullptr;
};

using VpiHandle = VpiObject*;

// §37.3.7: the categories an allocator can place an object into, used to derive
// its vpiAllocScheme. Keeping this separate from the scheme return values lets
// callers describe an allocation in intent ("this came from a frame") and have
// the mapping to the reported scheme live in one place.
enum class VpiAllocKind {
  kFrameOrThread,  // allocated with a frame or thread -> Automatic scheme
  kDynamic,        // allocated in dynamic memory (class object) -> Dynamic
  kOther,          // anything else -> the mandated Other default
};

// §37.3.7: map an allocation category to the vpiAllocScheme value that
// vpi_get(vpiAllocScheme) must report. Unrecognized/other allocations fall
// through to kVpiOtherScheme, satisfying the "all other objects" default.
int VpiAllocSchemeFor(VpiAllocKind kind);

}  // namespace delta
