#pragma once

#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "simulator/coverage_control.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_pli_types.h"

namespace delta {

class VpiContext {
 public:
  VpiContext() = default;
  ~VpiContext();

  void Attach(SimContext& sim_ctx);

  void SetScheduler(Scheduler* sched) { scheduler_ = sched; }

  VpiHandle RegisterSystf(VpiSystfData* data);

  // §36.3.2: resolve the effective registration for a system task/function
  // name, honouring the override rule. A user-provided PLI application
  // associated with the same name as a built-in overrides that built-in,
  // replacing its functionality, so the registry is consulted first: a matching
  // registration is the override to invoke, and only when none is present (a
  // null result) does the built-in stand. When several registrations share the
  // name the most recent one wins, so a later user application overrides an
  // earlier one.
  const VpiSystfData* ResolveSystf(const char* name) const;

  // §38.12: report the registration of the system task or system function
  // callback denoted by `obj` into the application-allocated structure
  // `systf_data_p`. The structure's memory belongs to the caller; this routine
  // only writes the stored s_vpi_systf_data fields into it. A null handle, a
  // null destination, or a handle that does not name a registered system
  // task/function callback leaves the destination untouched.
  void GetSystfInfo(VpiHandle obj, VpiSystfData* systf_data_p);

  // §38.8: report the registration of the simulation-related callback denoted
  // by `obj` into the application-allocated structure `cb_data_p`. The
  // structure's memory belongs to the caller; this routine only writes the
  // stored s_cb_data fields into it - it never allocates that storage. A null
  // destination, a null handle, or a handle that does not name a registered
  // simulation callback leaves the destination untouched. (Use GetSystfInfo for
  // a system task/function callback instead.)
  void GetCbInfo(VpiHandle obj, VpiCbData* cb_data_p);

  // §38.13: write the relevant simulation time into the application-allocated
  // structure `time_p`. The caller selects the form through `time_p->type`:
  // vpiSimTime delivers the raw 64-bit count in high/low; vpiScaledRealTime
  // delivers a real scaled to the object's timescale. A null obj uses the
  // simulation time unit; a time queue object reports the scheduled time of the
  // next future event, also in the simulation time unit. The structure's memory
  // belongs to the caller, so the routine only fills it and never allocates. A
  // null `time_p` leaves nothing to do.
  void GetTime(VpiHandle obj, VpiTime* time_p);

  // §38.10: retrieve the delays or pulse limits of `obj` into the
  // application-allocated structure `delay_p`. delay_p->no_of_delays selects
  // how many of the object's delays to retrieve and must be legal for the
  // object's category; delay_p->time_type controls the form of every value
  // written, and the type field of each da entry is ignored; delay_p->mtm_flag
  // and delay_p->pulsere_flag select the per-delay layout (Table 38-2). The
  // structure and its da array belong to the caller, so the routine only fills
  // them. A null delay_p, a null obj, or a null da leaves nothing to do; an
  // illegal no_of_delays records an error and writes nothing.
  void GetDelays(VpiHandle obj, VpiDelay* delay_p);

  // §38.32: set the delays or timing limits of `obj` from the
  // application-allocated `delay_p`, the write counterpart of GetDelays().
  // delay_p->no_of_delays selects how many delays to set and must be legal for
  // the object's category; delay_p->time_type gives the form of every source
  // value (the type field of each da entry is ignored); delay_p->mtm_flag and
  // delay_p->pulsere_flag select the per-delay layout (Table 38-4), with the
  // delays taken in source order. Only the fields the flags select are written,
  // so when pulsere_flag is clear the pulse limits keep their prior values. A
  // null delay_p, a null obj, or a null da changes nothing; an illegal
  // no_of_delays records an error (§38.2) and changes nothing.
  void PutDelays(VpiHandle obj, VpiDelay* delay_p);

  // §38.9: retrieve up to `num_of_bytes` of data saved under the save/restart
  // `id` into the caller-allocated buffer `data_loc`, returning the number of
  // bytes actually retrieved. The first call for an id reads from the start of
  // what was saved; each later call resumes where the previous one stopped. It
  // is acceptable to ask for fewer bytes than were saved. Asking for more than
  // remain is a warning: the bytes that are left are delivered, the rest of the
  // buffer is zero-filled, and the return value is the number actually read.
  // The routine is only legal from an application routine running for reason
  // cbStartOfRestart or cbEndOfRestart; any other failure (wrong reason, an
  // unknown id, or a null buffer) records an error and returns 0.
  int GetData(int id, char* data_loc, int num_of_bytes);

  // §38.9 / §38.32: populate the save/restart store for `id` with `len` bytes
  // from `data`, appending to whatever is already stored for that id. The
  // production writer is vpi_put_data() (§38.32); this entry point stands in
  // for it so the data vpi_get_data() reads back can be established.
  void SeedSaveData(int id, const char* data, int len);

  // §38.31: append `num_of_bytes` bytes from `data_loc` to the save/restart
  // store for `id`, returning the number of bytes written. The byte count must
  // be greater than zero and the source pointer must be supplied by the
  // application. The routine is only legal from an application routine running
  // for reason cbStartOfSave or cbEndOfSave; any failure (wrong reason, a
  // non-positive count, or a null source) detects an error and returns zero.
  // There is no limit on how many times an id may be written, and ids may be
  // written in any order; bytes for one id accumulate contiguously so that
  // vpi_get_data() (§38.9) can later read them back in chunks of any size.
  int PutData(int id, const char* data_loc, int num_of_bytes);

  // §38.33: associate `userdata` with `obj`, the storage location of a
  // user-defined system task or system function call instance, so a later
  // vpi_get_userdata() can read it back. Returns 1 on success. A null handle or
  // a handle that is not a system task/function call is an error (§38.2) and
  // returns 0, leaving no association made.
  int PutUserData(VpiHandle obj, void* userdata);

  // §38.14: read back the user-data value a prior vpi_put_userdata() (§38.33)
  // associated with `obj`, a system task or system function call instance. When
  // nothing was ever associated, or the handle is null or not such a call, the
  // routine yields null. A restart or a reset clears the field (§38.33), so a
  // read afterwards returns null until the application re-establishes it.
  void* GetUserData(VpiHandle obj);

  // §38.33: drop every system task/function call instance's user-data
  // association. Run when the simulation restarts or resets, so that after
  // either event a vpi_get_userdata() returns null until the application sets
  // the field again (from a cbEndOfRestart or cbEndOfReset routine).
  void ClearUserDataForRestartOrReset();

  // §38.13: set the simulation time unit, as a base-ten exponent of one second
  // (the unit the scheduler counts ticks in). vpi_get_time() uses it both as
  // the scaling reference for a scaled-real result and as the unit reported for
  // a null obj or a time queue object.
  void SetSimTimeUnit(int exponent) { sim_time_unit_ = exponent; }

  // §38.13: create a time queue object so vpi_get_time() can report the
  // scheduled time of the next future event.
  VpiHandle CreateTimeQueue();

  // §37.81: record the simulation time queue the vpi_iterate(vpiTimeQueue,
  // NULL) walk reports. The scheduler keeps this in step with the pending-event
  // calendar; each slot names a simulation time that still holds events. The
  // iteration sorts them into increasing time order, drops the current-time
  // slot unless events remain before its read-only synch region, and yields a
  // time queue object for each surviving slot (an empty result returns NULL).
  void SetTimeQueueSlots(std::vector<VpiTimeQueueSlot> slots) {
    time_queue_slots_ = std::move(slots);
  }

  // §38.21: return a handle to the object named `name`, which may be a simple
  // or a hierarchical name. With a null scope the name is searched for from the
  // top level of the design hierarchy; with a scope the search is confined to
  // that scope's contents. A protected scope object, or a hierarchical name
  // that passes through a protected scope, makes the call an error (no handle).
  VpiHandle HandleByName(const char* name, VpiHandle scope);
  VpiHandle HandleByIndex(int index, VpiHandle parent);

  // §38.20: return a handle to the index-selected subobject of `parent` named
  // by the `num_index` indices in `index_array`. Like vpi_handle_by_index(),
  // the reference object must carry the access-by-index property and must not
  // be protected, or the call is an error. The indices are applied leftmost
  // first, following the array dimension declaration from the leftmost to the
  // rightmost range, optionally ending in a bit-select index. When the indices
  // do not form a legal SystemVerilog index select expression the result is a
  // null handle.
  VpiHandle HandleByMultiIndex(int num_index, const int* index_array,
                               VpiHandle parent);
  VpiHandle Handle(int type, VpiHandle ref);
  VpiHandle Iterate(int type, VpiHandle ref);
  VpiHandle Scan(VpiHandle iterator);
  void GetValue(VpiHandle obj, VpiValue* value);
  VpiHandle PutValue(VpiHandle obj, VpiValue* value, VpiTime* time, int flags);
  VpiHandle RegisterCb(VpiCbData* data);
  int RemoveCb(VpiHandle cb_handle);
  int ExecuteCallback(VpiHandle cb_handle);
  void RegisterCbValueChange(const VpiCbData& data);

  // §38.36.3: deliver every active callback registered for the given action or
  // feature reason. Each routine receives a copy of its s_cb_data whose reason
  // field holds the reason for the callback; when a non-null obj or user_data
  // is supplied the simulator fills that field before the routine runs (for
  // example, the timing-check handle for cbTchkViolation, the new scope handle
  // for cbInteractiveScopeChange, or the unresolved name for
  // cbUnresolvedSystf). Returns how many callbacks were delivered.
  int DispatchCallbacks(int reason, VpiHandle obj = nullptr,
                        void* user_data = nullptr);

  // §38.36.3: a reset delivers cbStartOfReset at the start of the operation and
  // cbEndOfReset once it has completed. This is the single path used whether
  // the reset was requested directly or through vpi_control(vpiReset, ...).
  int DispatchReset();

  // §38.36.3: a restart first removes every registered callback except the
  // restart callbacks, then delivers cbStartOfRestart followed by
  // cbEndOfRestart, so the only callbacks that exist across a restart are those
  // two.
  int DispatchRestart();

  int Get(int property, VpiHandle obj);

  // §38.7: read a 64-bit integer object property (one whose type is PLI_INT64),
  // returning the value at full width instead of the PLI_INT32 vpi_get()
  // yields. Querying a protected object is an error, and on any error the value
  // returned is vpiUndefined.
  PLI_INT64 Get64(int property, VpiHandle obj);

  // §37.10 detail 7: the smallest time precision over every module object the
  // context knows about, used to answer vpi_get(vpiTimePrecision/vpiTimeUnit)
  // for a null handle.
  int SmallestModuleTimePrecision() const;

  const char* GetStr(int property, VpiHandle obj);
  // §38.11: computes the raw string value for a property, pointing into the
  // object's own storage (or null). GetStr() copies the result into the shared
  // temporary buffer the clause mandates; this helper does not.
  const char* GetStrRaw(int property, VpiHandle obj);
  // Annex C.2.4: the deprecated vpi_free_object() routine. It was renamed
  // vpi_release_handle(), so this name no longer performs a release: a call is
  // flagged as deprecated and reports failure. Use ReleaseHandleStatus() (the
  // vpi_release_handle() backend) for the live operation.
  int FreeObject(VpiHandle obj);
  // §38.4: vpi_control() passes an operation-specific request from the PLI
  // application to the simulator. arg0..arg2 carry the operation's additional
  // integer arguments (the diagnostic level for vpiStop/vpiFinish, or the
  // stop/reset/diagnostics values for vpiReset); scope carries the vpiHandle
  // argument of vpiSetInteractiveScope. Returns 1 on success, 0 on failure.
  int Control(int operation, int arg0 = 0, int arg1 = 0, int arg2 = 0,
              VpiHandle scope = nullptr);

  // §40.5.3: control of coverage collection is requested through vpi_control()
  // using the coverage control constants of §40.5.1. `operation` selects the
  // action: vpiCoverageStart/Stop/Reset/Check apply the §40.3.2.1 control rules
  // to the scope named by `scope_handle` (an instance or assertion handle);
  // vpiCoverageSave applies the §40.3.2.5 rules and vpiCoverageMerge the
  // §40.3.2.4 rules to the coverage database located by `name`. `coverage_type`
  // is one of the §40.5.1 coverage type properties.
  //
  // Statement, toggle, and FSM coverage are not individually controllable, so
  // the Start/Stop/Reset/Check actions act on the scope the handle names as a
  // whole rather than on any per-statement, per-signal, or per-FSM object. The
  // return is the §40.3.1 status value the equivalent system function produces,
  // so the detailed outcome - and the collection-state change it reflects - is
  // observable to the caller.
  int ControlCoverage(int operation, int coverage_type, VpiHandle scope_handle,
                      const std::string& name);

  // §40.5.3: the coverage-control state vpi_control() drives. It applies the
  // same §40.3.2.1/.4/.5 rules the $coverage_* system functions use, so tests
  // can register scopes and databases and observe the rules being applied.
  CoverageControlState& GetCoverageControlState() { return coverage_control_; }

  bool ChkError(VpiErrorInfo* info);

  // §38.17: capture the simulator's invocation command line. Following the
  // standard argv convention, entry zero is the tool's own name and the
  // remaining entries are the invocation options; GetVlogInfo() reports these
  // back through the s_vpi_vlog_info structure. Placing the tool name at entry
  // zero here is what makes that requirement hold for every later query.
  void SetInvocationArguments(const std::string& tool_name,
                              const std::vector<std::string>& options);

  // §38.17: fill the result structure with the invocation option count (argc),
  // the option values (argv), and the product and version strings. Returns true
  // on success and false when the information cannot be supplied.
  bool GetVlogInfo(VpiVlogInfo* info);

  // §38.5: flush the output buffers for the simulator's output channel and the
  // current log file. Each channel accumulates written text in an in-memory
  // buffer until it is flushed; flushing commits any pending text into the
  // channel's committed stream and empties the buffer. Returns 0 on success and
  // nonzero on failure, in which case the buffers are left untouched.
  int Flush();

  // Support hooks for the flush model. Writes feed buffered text into either
  // channel; the buffer accessors report what is still pending and the flushed
  // accessors report what a flush has committed.
  void WriteOutputChannel(std::string_view text) {
    output_channel_buffer_.append(text);
  }
  void WriteLogFile(std::string_view text) { log_file_buffer_.append(text); }
  const std::string& OutputChannelBuffer() const {
    return output_channel_buffer_;
  }
  const std::string& LogFileBuffer() const { return log_file_buffer_; }
  const std::string& OutputChannelFlushed() const {
    return output_channel_flushed_;
  }
  const std::string& LogFileFlushed() const { return log_file_flushed_; }
  // Forces the next Flush() down the failure path so the nonzero return can be
  // exercised.
  void SetFlushShouldFail(bool fail) { flush_should_fail_ = fail; }

  // §38.27: open a file for writing and return a multichannel descriptor (mcd)
  // naming it. A fresh descriptor selects a single channel drawn from the bits
  // that vpi_mcd_open() is allowed to use: channel 1 (the LSB) is reserved for
  // the tool's own output channel and log file, and channel 32 (the MSB) is
  // reserved for an fd from $fopen, so neither is ever handed out here. These
  // mcds share one namespace with the mcds $fopen returns, so a file that is
  // already open - whether opened by an earlier vpi_mcd_open() or by $fopen -
  // yields its existing descriptor instead of a new one. Returns 0 on error,
  // including when no channel is free.
  PLI_UINT32 McdOpen(const std::string& filename);

  // §38.24: close the file(s) named by a multichannel descriptor. Because the
  // channels are discrete bits of the integer mcd, several are closed at once -
  // every set bit that names an open channel is freed and the file it named is
  // dropped from the shared namespace (the same namespace $fopen uses, so an fd
  // opened there can be closed here too). Descriptor 1 (the LSB) is predefined
  // for the tool's own output channel and log file and cannot be closed; any
  // bit that names no closeable channel is left untouched. Returns 0 when every
  // requested channel was closed, otherwise the mcd of the channels left open.
  PLI_UINT32 McdClose(PLI_UINT32 mcd);

  // Support hooks for the mcd-open model. The fopen registrar records that a
  // file is already open on a given descriptor in the shared namespace; the
  // accessors let a test observe which descriptor names a file; the failure
  // hook forces the next open down its error return.
  void RegisterFopenMcdFile(const std::string& filename, PLI_UINT32 mcd) {
    mcd_open_files_[filename] = mcd;
    mcd_allocated_channels_ |= mcd;
  }
  PLI_UINT32 McdForFile(const std::string& filename) const {
    auto it = mcd_open_files_.find(filename);
    return it == mcd_open_files_.end() ? 0u : it->second;
  }
  bool IsMcdFileOpen(const std::string& filename) const {
    return mcd_open_files_.find(filename) != mcd_open_files_.end();
  }
  void SetMcdOpenShouldFail(bool fail) { mcd_open_should_fail_ = fail; }

  // §38.25: flush the output buffers for the file(s) named by a multichannel
  // descriptor. Because the channels are discrete bits of the integer mcd, one
  // call names several files; the buffered output of every named channel is
  // committed into its committed stream and the buffer emptied. Returns 0 on
  // success and nonzero on failure, in which case the buffers are left
  // untouched so nothing pending is lost.
  PLI_INT32 McdFlush(PLI_UINT32 mcd);

  // §38.26: return the name of the file a single-channel descriptor names. The
  // descriptor is looked up in the shared mcd/fd namespace - the one
  // vpi_mcd_open() and $fopen populate (§38.27, §21.3.1) - so cd may be an mcd
  // channel or an fd from $fopen with its MSB set. The name is handed back
  // through a buffer reused on every call, so a pointer from an earlier call is
  // overwritten here; a caller that needs to keep the string must copy it.
  // Returns NULL on error, including a descriptor that names no open file.
  PLI_BYTE8* McdName(PLI_UINT32 cd);

  // §38.28: write already-formatted text to every file the descriptor names.
  // Each channel is a discrete bit of the integer mcd, so one call writes to
  // several files at once; bit 0 names channel 1 (the tool's output channel and
  // log file), and the MSB names a file opened as an fd by $fopen. The text is
  // appended to each named channel's output buffer (the same buffer §38.25
  // flushes). Returns the number of characters written.
  PLI_INT32 McdPrintf(PLI_UINT32 mcd, std::string_view text);

  // §38.30: write already-formatted text to both the output channel of the tool
  // that invoked the PLI application and the current tool log file. Unlike
  // McdPrintf() there is no descriptor: the destination is always the tool's
  // own output channel and log file (the §38.5 buffers), so the same text is
  // appended to each. Returns the number of characters written.
  PLI_INT32 Printf(std::string_view text);

  // Support hooks for the mcd-flush model. The writer feeds buffered text onto
  // a single channel (the one set bit naming the file); the accessors report
  // what is still pending on a channel and what a flush has committed; the
  // failure hook forces the next flush down its nonzero return.
  void WriteMcdChannel(PLI_UINT32 channel, std::string_view text) {
    mcd_channel_buffers_[channel].append(text);
  }
  const std::string& McdChannelBuffer(PLI_UINT32 channel) const {
    auto it = mcd_channel_buffers_.find(channel);
    return it == mcd_channel_buffers_.end() ? empty_mcd_buffer_ : it->second;
  }
  const std::string& McdChannelFlushed(PLI_UINT32 channel) const {
    auto it = mcd_channel_flushed_.find(channel);
    return it == mcd_channel_flushed_.end() ? empty_mcd_buffer_ : it->second;
  }
  void SetMcdFlushShouldFail(bool fail) { mcd_flush_should_fail_ = fail; }

  VpiHandle HandleMulti(int type, VpiHandle ref1, VpiHandle ref2);

  // §38.3: report whether two handles reference the same underlying simulation
  // object at the moment of the call. Returns 1 (TRUE) when they do and that
  // object exists, 0 (FALSE) otherwise. The comparison resolves each handle to
  // the representative of the object it denotes, so handles that alias the same
  // object compare equal even though their handle pointers differ; this is why
  // object equivalence cannot be settled with a C "==" comparison.
  int CompareObjects(VpiHandle obj1, VpiHandle obj2);

  // §37.2.1: hand back a handle that refers to an existing object. The standard
  // lets a tool answer a request for a handle to an object it can already name
  // either with the same handle or with a fresh, distinct one; this routine
  // takes the latter option, allocating a new handle (a different pointer) that
  // nonetheless denotes the same underlying object. Because the two handles
  // refer to one object they are equivalent: vpi_compare_objects() reports them
  // equal even though a C "==" of the handle pointers would not. A null object
  // names nothing, so the result is null.
  VpiHandle CreateHandleFor(VpiHandle object);

  // §37.2.2: release a handle, the operation vpi_release_handle() performs. The
  // handle is marked released so it is no longer a live handle to its object;
  // the object itself is left in place. Because the flag is per-handle, a
  // distinct handle to the same object - one another VPI program may still hold
  // - is unaffected and continues to refer to that object. A null handle names
  // nothing to release. Idempotent.
  void ReleaseHandle(VpiHandle handle);

  // §38.38: the public vpi_release_handle() routine. It frees the memory a VPI
  // routine allocated for a handle and reports whether it did so - 1 on success
  // and 0 on failure. The routine shall not be called on an invalid handle, so
  // a null, already-released, or otherwise invalid handle has no live memory to
  // free and the call fails with 0. An iterator object (from vpi_iterate(),
  // §38.21) owns storage that vpi_scan() reclaims only once a traversal runs to
  // its end; releasing one before then frees that storage directly, which is
  // how a program that breaks out of an iteration loop early reclaims it. For
  // any other handle, freeing it is the §37.2.2 release operation above.
  PLI_INT32 ReleaseHandleStatus(VpiHandle handle);

  // §37.2.2: observe whether a handle has been released. False for a null
  // handle (there is nothing to have released).
  bool HandleReleased(VpiHandle handle) const;

  // §37.2.4: whether a handle is valid. A handle is valid from the time of its
  // creation until it is released (§37.2.2), until the object it refers to
  // ceases to exist (§38.3 object existence), or until the tool terminates; at
  // any other time it is invalid. Termination tears down the context itself, so
  // the live cases this predicate distinguishes are release and the object
  // ceasing to exist. A null handle refers to nothing and is never valid. A VPI
  // program is required not to use an invalid handle to refer to an object, nor
  // to release one; this predicate reports the validity those rules turn on.
  bool HandleValid(VpiHandle handle) const;

  // §37.2.2 (restart): whether a handle survives a simulation restart. Only the
  // handles to cbStartOfRestart and cbEndOfRestart callbacks survive; every
  // other handle is released by the restart so those two callbacks can run.
  bool HandleSurvivesRestart(VpiHandle handle) const;

  // §37.2.2 (restart): release every handle a simulation restart releases - all
  // of them except the two restart-callback handles (see
  // HandleSurvivesRestart). DispatchRestart() invokes this so a restart applies
  // the rule.
  void ReleaseHandlesForRestart();

  // §37.2.2 (frame/thread free): when the simulator frees objects belonging to
  // a frame or thread, it releases all handles to those objects and to any
  // subelement of them; handles to callbacks placed on any of these objects are
  // released as well. `root` is the freed object; its subelements are its
  // children, walked recursively.
  void ReleaseFrameOrThreadObject(VpiHandle root);

  // §37.2.2 (class reclaim): when the simulator reclaims the memory of a class
  // object, it releases the handle to the class object, to any of its automatic
  // data members, and to any subelement of those automatic data members;
  // handles to callbacks placed on any of these are released too. Static data
  // members persist and are not released (NOTE 3 of §37.2.2 - a static local in
  // a task/function does not belong to a frame or thread either).
  void ReleaseClassObject(VpiHandle class_object);

  // §36.12.2.2: Mechanism 2 - selection of the default VPI compatibility mode
  // run by the host simulator. This is the means the simulation provider makes
  // available to set, for an entire simulation run, the compatibility mode that
  // governs every VPI application not bound to a mode through the compile-based
  // scheme of Mechanism 1 (§36.12.2.1). Only one default mode is selectable for
  // a given run: the first selection fixes it and a later request for a
  // different mode is refused (returns false) so the run keeps one consistent
  // default; re-selecting the mode already in force is accepted. `mode` is a
  // vpiCompatibilityMode value, with 0 meaning no compatibility mode (the
  // native, current-standard data model). Returns true when the requested mode
  // is the one in force after the call.
  bool SetDefaultCompatibilityMode(int mode);

  // §36.12.2.2: the default VPI compatibility mode currently in force for the
  // simulation run, as established by SetDefaultCompatibilityMode. Zero when no
  // mode has been selected, in which case applications observe the native
  // current-standard behavior.
  int DefaultCompatibilityMode() const { return default_compat_mode_; }

  // §36.12.2.2: the compatibility mode that actually governs a particular VPI
  // application. An application bound to a mode through Mechanism 1 carries
  // that mode in its recompiled entry points, so the run-wide default does not
  // apply to it - when `uses_mechanism1` is true the application's own
  // `mechanism1_mode` governs. Every application not using the compile-based
  // scheme is governed by the run-wide default instead. This is how an
  // application needing a mode different from the default obtains one: by using
  // the compile-based mechanism.
  int EffectiveCompatibilityMode(bool uses_mechanism1,
                                 int mechanism1_mode) const;

  VpiHandle CreateModule(std::string_view name, std::string full_name);

  VpiHandle CreatePort(std::string_view name, int direction, VpiHandle parent);

  VpiHandle CreateParameter(std::string_view name, int int_value);

  // §37.49: register an assertion object under one of the assertion-class kinds
  // so that it is reachable as a top-level assertion (the circle relation) by a
  // null-referenced vpi_iterate(vpiAssertion, NULL).
  VpiHandle CreateAssertion(std::string_view name, int type);

  VpiHandle CreateNetObj(std::string_view name, Net* net_ptr, int width);

  // §38.35: build a static unpacked array object with one element child per
  // supplied variable. `array_type` is the vpiArrayType the array reports;
  // `dim_indices` gives the declared index values of each unpacked dimension in
  // left-to-right order. Each element child is created as a vpiReg over the
  // matching variable, keyed by its flat ordinal (rightmost dimension varying
  // fastest), so vpi_put_value_array() can locate and fill elements.
  VpiHandle CreateRegArray(std::string_view name, int array_type,
                           const std::vector<std::vector<int>>& dim_indices,
                           const std::vector<Variable*>& elements);

  // §38.35: write values into contiguous elements of a static unpacked array.
  // arrayvalue_p selects the element encoding and flags; index_p gives the
  // starting element's coordinate (one entry per unpacked dimension); num is
  // how many consecutive elements to set. Applies vpiNoDelay semantics only.
  void PutValueArray(VpiHandle obj, VpiArrayValue* arrayvalue_p, int* index_p,
                     unsigned int num);

  // §38.16: read values from contiguous elements of a static unpacked array.
  // arrayvalue_p->format selects the element encoding written back; index_p
  // gives the starting element's coordinate (one entry per unpacked dimension);
  // num is how many consecutive elements to retrieve, taken with the rightmost
  // dimension varying fastest. By default the values land in VPI-owned storage
  // pointed to by the value arm; with vpiUserAllocFlag the caller's own buffer
  // is filled instead. On any error the value arm is set to NULL.
  void GetValueArray(VpiHandle obj, VpiArrayValue* arrayvalue_p, int* index_p,
                     unsigned int num);

  const std::vector<VpiSystfData>& RegisteredSystfs() const { return systfs_; }

  const std::vector<VpiCbData>& RegisteredCallbacks() const {
    return callbacks_;
  }

  // §36.9.1: the registration of system tasks shall occur prior to elaboration
  // or the resolution of references. Marking elaboration as started closes the
  // window in which RegisterSystf will accept new registrations.
  void MarkElaborationStarted() { elaboration_started_ = true; }
  bool ElaborationStarted() const { return elaboration_started_; }

  // §36.10.2: the tool-lifecycle phase the VPI interface is currently in. It
  // gates which routines and callback reasons a PLI application may use. The
  // default is the full phase, so ordinary (post-compile) VPI use is
  // unrestricted; InvokeVlogStartupRoutines narrows it to the startup phase
  // while the vlog_startup_routines[] array executes.
  void SetToolPhase(VpiToolPhase phase) { tool_phase_ = phase; }
  VpiToolPhase ToolPhase() const { return tool_phase_; }

  // §38.36.2: the scheduler records when simulation has advanced past time zero
  // into a time slice, and when it has reached the read-only synch region of a
  // time slice. vpi_register_cb() consults these to reject the zero-delay
  // simulation-time callbacks the standard forbids in those situations.
  void SetSimulationProgressedIntoTimeSlice(bool progressed) {
    sim_progressed_into_time_slice_ = progressed;
  }
  bool SimulationProgressedIntoTimeSlice() const {
    return sim_progressed_into_time_slice_;
  }
  void SetAtReadOnlySynchTime(bool at_read_only) {
    at_read_only_synch_time_ = at_read_only;
  }
  bool AtReadOnlySynchTime() const { return at_read_only_synch_time_; }

  bool StopRequested() const { return stop_requested_; }
  bool FinishRequested() const { return finish_requested_; }

  // §38.4: the diagnostic message level vpi_control() forwarded with the most
  // recent vpiStop/vpiFinish request (the same value $stop/$finish would carry,
  // see 20.2).
  int StopDiagLevel() const { return stop_diag_level_; }
  int FinishDiagLevel() const { return finish_diag_level_; }

  // §38.4: a reset requested through vpi_control(vpiReset, ...) and the three
  // arguments it carried (the same values passed to the $reset task, see D.8).
  bool ResetRequested() const { return reset_requested_; }
  int ResetStopValue() const { return reset_stop_value_; }
  int ResetResetValue() const { return reset_reset_value_; }
  int ResetDiagValue() const { return reset_diag_value_; }

  // §38.4: the scope vpi_control(vpiSetInteractiveScope, ...) most recently
  // made the tool's interactive scope.
  VpiHandle InteractiveScope() const { return interactive_scope_; }

  // §37.43 detail 4: record which frame is the one currently active. There is
  // at most one active frame at a time in a given thread, and an application
  // reaches it through vpi_handle(vpiFrame, NULL) (see Handle).
  void SetActiveFrame(VpiHandle frame) { active_frame_ = frame; }
  VpiHandle ActiveFrame() const { return active_frame_; }

  // §37.42 detail 3: record which system task or function call is currently
  // invoking a PLI application. An application reaches it through
  // vpi_handle(vpiSysTfCall, NULL) (see Handle); null when no system tf call is
  // active.
  void SetCurrentSystfCall(VpiHandle call) { current_systf_call_ = call; }
  VpiHandle CurrentSystfCall() const { return current_systf_call_; }

  // §37.82: record the system task call that established the active time
  // format, i.e. the $timeformat() call. An application reaches it through
  // vpi_handle(vpiActiveTimeFormat, NULL) (see Handle). It stays null until
  // $timeformat() runs, which is what makes that traversal return NULL when no
  // time format has been set (detail 1).
  void SetActiveTimeFormatCall(VpiHandle call) {
    active_time_format_call_ = call;
  }
  VpiHandle ActiveTimeFormatCall() const { return active_time_format_call_; }

  const VpiErrorInfo& LastError() const { return last_error_; }

  // §38.2: the error status is reset by any VPI routine call except
  // vpi_chk_error(). The C entry points clear the pending error here on entry
  // before doing their work, so vpi_chk_error() reports only the outcome of the
  // most recent routine; a failing routine then records a fresh error.
  void ResetErrorStatus() { last_error_ = {}; }

 private:
  VpiHandle AllocObject();

  // §37.2.2: release one handle plus the handles to every callback placed on
  // the object it names. Building block for the simulation-event release rules.
  void ReleaseHandleWithCallbacks(VpiObject* object);

  // §37.2.2: release a handle, all subelement handles reachable through its
  // children, and the callbacks on any of them. Used by the frame/thread-free
  // and class-reclaim release rules.
  void ReleaseHandleSubtree(VpiObject* root);

  std::vector<VpiSystfData> systfs_;
  std::vector<VpiCbData> callbacks_;
  std::vector<VpiHandle> cb_handles_;
  std::unordered_map<std::string_view, VpiObject*> object_map_;
  std::vector<VpiObject*> all_objects_;
  Scheduler* scheduler_ = nullptr;
  // §38.13: the simulation time unit (base-ten exponent of one second) the
  // scheduler's tick count is expressed in; the reference vpi_get_time() scales
  // a scaled-real result against.
  int sim_time_unit_ = 0;
  // §37.81: the pending entries of the simulation time queue, the source the
  // vpi_iterate(vpiTimeQueue, NULL) walk filters and sorts. Empty until the
  // scheduler records pending events, which is why an idle queue iterates to
  // NULL.
  std::vector<VpiTimeQueueSlot> time_queue_slots_;
  bool elaboration_started_ = false;
  // §36.10.2: see SetToolPhase. Defaults to the full phase so VPI use outside
  // the startup window is unrestricted.
  VpiToolPhase tool_phase_ = VpiToolPhase::kFull;
  bool stop_requested_ = false;
  bool finish_requested_ = false;
  int stop_diag_level_ = 0;
  int finish_diag_level_ = 0;
  bool reset_requested_ = false;
  int reset_stop_value_ = 0;
  int reset_reset_value_ = 0;
  int reset_diag_value_ = 0;
  VpiHandle interactive_scope_ = nullptr;
  // §37.43 detail 4: the frame currently active, returned by
  // vpi_handle(vpiFrame, NULL).
  VpiHandle active_frame_ = nullptr;
  // §37.42 detail 3: the system task or function call currently invoking a PLI
  // application, returned by vpi_handle(vpiSysTfCall, NULL).
  VpiHandle current_systf_call_ = nullptr;

  // §37.82: the $timeformat() call that set the active time format, returned by
  // vpi_handle(vpiActiveTimeFormat, NULL). Null until $timeformat() is called.
  VpiHandle active_time_format_call_ = nullptr;

  // §36.12.2.2: the run-wide default VPI compatibility mode selected through
  // Mechanism 2 (a vpiCompatibilityMode value; 0 = native current standard),
  // and whether one has been selected yet. The selection is fixed for the
  // simulation run once made, so only one default mode is selectable per run.
  int default_compat_mode_ = 0;
  bool default_compat_mode_selected_ = false;

  // §38.5: the simulator's output channel and current log file each hold
  // written text in an in-memory buffer until vpi_flush() commits it. A flush
  // appends each buffer to its committed stream and clears the buffer.
  std::string output_channel_buffer_;
  std::string output_channel_flushed_;
  std::string log_file_buffer_;
  std::string log_file_flushed_;
  // Test hook that drives vpi_flush() down its failure return.
  bool flush_should_fail_ = false;

  // §38.27: descriptors handed out by vpi_mcd_open(), keyed by file name so a
  // repeated open of the same file returns the descriptor it already holds.
  // mcd_allocated_channels_ marks every channel bit currently in use - both the
  // ones this routine assigned and any seeded from $fopen - so a fresh open can
  // pick an unused channel. Channel 1 (LSB) and channel 32 (MSB) are reserved
  // and never selected.
  std::unordered_map<std::string, PLI_UINT32> mcd_open_files_;
  PLI_UINT32 mcd_allocated_channels_ = 0;
  // Test hook that drives vpi_mcd_open() down its error return.
  bool mcd_open_should_fail_ = false;

  // §38.25: each open mcd channel holds the text written to its file in an
  // in-memory buffer until vpi_mcd_flush() commits it. A flush appends each
  // named channel's buffer to its committed stream and clears the buffer. Keyed
  // by the single channel bit so one descriptor's several channels are flushed
  // together.
  std::unordered_map<PLI_UINT32, std::string> mcd_channel_buffers_;
  std::unordered_map<PLI_UINT32, std::string> mcd_channel_flushed_;
  // Test hook that drives vpi_mcd_flush() down its failure return.
  bool mcd_flush_should_fail_ = false;
  // Returned by the channel accessors when a channel has no buffered or flushed
  // text, so they can hand back a reference without inserting an entry.
  const std::string empty_mcd_buffer_;

  // §38.26: the single buffer vpi_mcd_name() reuses for its result, so each
  // call overwrites the previous returned value. Separate from get_str_buffer_.
  std::string mcd_name_buffer_;

  VpiErrorInfo last_error_ = {};

  // §38.9: the reason of the callback whose application routine is currently
  // executing, or -1 when no callback is running. vpi_get_data() consults this
  // to enforce that it is only called from a cbStartOfRestart/cbEndOfRestart
  // routine; DispatchCallbacks sets and restores it around each cb_rtn call.
  int current_callback_reason_ = -1;

  // §38.36.2: simulation-time-callback placement state, driven by the scheduler
  // as simulation advances. The first is set once execution has progressed into
  // a time slice (past time zero); the second while the time slice is in its
  // read-only synch region. Both gate the zero-delay placement errors in
  // RegisterCb. Default: simulation has not yet entered any time slice.
  bool sim_progressed_into_time_slice_ = false;
  bool at_read_only_synch_time_ = false;

  // §38.9 / §38.32: the save/restart byte store keyed by save/restart id, plus
  // a per-id read cursor so successive vpi_get_data() calls resume where the
  // previous one stopped. SeedSaveData appends bytes (standing in for
  // vpi_put_data, §38.32); GetData reads and advances the cursor.
  std::unordered_map<int, std::vector<char>> save_data_;
  std::unordered_map<int, std::size_t> save_data_cursor_;

  // §40.5.3: the coverage-collection state driven by vpi_control(). It carries
  // the §40.3.2.1/.4/.5 control rules so a coverage control request applies the
  // same semantics as the equivalent $coverage_* system function.
  CoverageControlState coverage_control_;

  std::string product_ = "DeltaHDL";
  std::string version_ = "0.1.0";

  // §38.17: the invocation command line reported by vpi_get_vlog_info(). The
  // owning strings live in invocation_args_ (entry zero is the tool name); the
  // pointer array handed back as argv is rebuilt into invocation_argv_ on each
  // query so every entry references a NUL-terminated copy of one token.
  std::vector<std::string> invocation_args_;
  std::vector<const char*> invocation_argv_;

  std::vector<std::string> str_pool_;

  // §38.11: vpi_get_str() places its result in one temporary buffer that every
  // call reuses, so an earlier returned pointer is clobbered by a later call.
  // It is deliberately separate storage from str_pool_ (the buffer that backs
  // s_vpi_value strings), which the clause requires to be a different buffer.
  std::string get_str_buffer_;

  // §38.15: vpi_get_value() owns the memory for the vector arm of the value
  // union; each retrieval keeps its s_vpi_vecval array alive here until the
  // context is torn down. Inner vectors own their own storage, so growing the
  // outer pool never invalidates a previously handed-out array pointer.
  std::vector<std::vector<VpiVectorVal>> vec_pool_;

  // §38.15: likewise the routine owns the s_vpi_strengthval array handed back
  // for the strength arm of the value union.
  std::vector<std::vector<VpiStrengthVal>> strength_pool_;

  // §38.16: by default vpi_get_value_array() returns the retrieved section in
  // VPI-allocated, read-only storage. One reusable buffer backs the value arm;
  // a subsequent call overwrites it, so the caller must copy out anything it
  // needs to keep.
  std::vector<unsigned char> value_array_storage_;
};

Region RegionForPliCallback(int reason);

bool IsOneShotPliCallback(int reason);

VpiContext& GetGlobalVpiContext();
void SetGlobalVpiContext(VpiContext* ctx);

// §36.9.1: the intended use model places a reference to a registration
// routine in the vlog_startup_routines[] array. Each entry is a function that
// takes no arguments and returns nothing, and the array is conventionally
// null-terminated.
using VlogStartupRoutine = void (*)();

// §36.9.1: walking the vlog_startup_routines[] array calls each non-null
// entry in order, giving each routine its chance to register user-defined
// system tasks and functions before elaboration begins. Iteration stops at
// the first null sentinel.
void InvokeVlogStartupRoutines(VlogStartupRoutine* routines);

}  // namespace delta
