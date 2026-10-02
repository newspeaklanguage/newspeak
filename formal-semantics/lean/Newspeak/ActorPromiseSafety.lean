import Newspeak.ActorExecution

namespace Newspeak

namespace PromiseState

/-- A promise state to which no waiter can subsequently be registered and
    from which the operational semantics has no settlement transition. -/
def Terminal : PromiseState → Prop
  | .pending _ _ => False
  | .fulfilled _ _ => True
  | .broken _ _ => True

end PromiseState

def PromiseTerminalAt (world : ActorWorld) (promise : PromiseId) : Prop :=
  ∃ state, world.promises promise = some state ∧ state.Terminal

theorem PromiseState.Terminal.not_pending
    {state : PromiseState} (terminal : state.Terminal)
    {owner : ActorId} {waiters : List PromiseWaiter} :
    state ≠ .pending owner waiters := by
  cases state <;> simp_all [PromiseState.Terminal]

/-- The platform operation that copies or shares a deeply immutable value may
    modify actor heaps, but it must not mutate the global promise table. -/
def ValueTransferPreservesPromiseStore
    (valueTransfer : ValueTransferRelation) : Prop :=
  ∀ world source destination object after represented,
    valueTransfer world source destination object after represented →
      after.promises = world.promises

@[simp] theorem ActorWorld.emitPacket_preserves_promises
    (world : ActorWorld) (source destination : ActorId)
    (payload : ActorPacketPayload) :
    (world.emitPacket source destination payload).promises = world.promises := by
  by_cases same : source = destination <;> simp [ActorWorld.emitPacket, same]

@[simp] theorem ActorWorld.installNextFarReference_preserves_promises
    (world : ActorWorld) (actor : ActorId) (object : ObjRef) :
    (world.installNextFarReference actor object).1.promises = world.promises := by
  rfl

theorem RemoteRepresentation.preserves_promise_store
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    {world after : ActorWorld} {source destination : ActorId}
    {reference represented : EventualRef}
    (relation : RemoteRepresentation isValue valueTransfer world source
      destination reference after represented) :
    after.promises = world.promises := by
  cases relation with
  | same => rfl
  | value _ _ transfer => exact transferPreserves _ _ _ _ _ _ transfer
  | farHome | farPass | promise => rfl
  | nearFar => rfl

theorem RemoteArgumentListRepresentation.preserves_promise_store
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    {source destination : ActorId} {world after : ActorWorld}
    {arguments represented : List EventualRef}
    (relation : RemoteArgumentListRepresentation isValue valueTransfer
      source destination world arguments after represented) :
    after.promises = world.promises := by
  induction relation with
  | nil => rfl
  | cons head tail ih =>
      exact ih.trans (head.preserves_promise_store transferPreserves)

theorem RemoteMessageRepresentation.preserves_promise_store
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    {source destination : ActorId} {world after : ActorWorld}
    {message represented : EventualMessage}
    (relation : RemoteMessageRepresentation isValue valueTransfer source
      destination world message after represented) :
    after.promises = world.promises := by
  cases relation with
  | message arguments =>
      exact arguments.preserves_promise_store transferPreserves

theorem PromiseSettlement.preserves_other_promise
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    {world after : ActorWorld} {settledPromise otherPromise : PromiseId}
    {disposition : SettlementDisposition} {source : ActorId}
    {result : EventualRef} {history : List EventId}
    (different : otherPromise ≠ settledPromise)
    (settlement : PromiseSettlement isValue valueTransfer world settledPromise
      disposition source result history after) :
    after.promises otherPromise = world.promises otherPromise := by
  cases settlement with
  | @settle world representedWorld _ owner source waiters disposition result
      represented history pending subset representation resultAfter =>
      subst after
      simp only [commitPromiseSettlement]
      rw [ActorWorld.wakeAllWaiters_preserves_promises]
      rw [FiniteStore.install_away _ _ different]
      exact congrArg (fun store => store otherPromise)
        (representation.preserves_promise_store transferPreserves)

theorem PromiseSettlement.establishes_terminal
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {world after : ActorWorld}
    {promise : PromiseId} {disposition : SettlementDisposition}
    {source : ActorId} {result : EventualRef} {history : List EventId}
    (settlement : PromiseSettlement isValue valueTransfer world promise
      disposition source result history after) :
    PromiseTerminalAt after promise := by
  rcases settlement.result_is_terminal with ⟨owner, represented, lookup⟩
  cases disposition
  · exact ⟨.fulfilled owner represented, lookup, trivial⟩
  · exact ⟨.broken owner represented, lookup, trivial⟩

theorem PromiseSettlement.requires_pending
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {world after : ActorWorld}
    {promise : PromiseId} {disposition : SettlementDisposition}
    {source : ActorId} {result : EventualRef} {history : List EventId}
    (settlement : PromiseSettlement isValue valueTransfer world promise
      disposition source result history after) :
    ∃ owner waiters,
      world.promises promise = some (.pending owner waiters) := by
  cases settlement with
  | settle pending => exact ⟨_, _, pending⟩

theorem RouteEventualMessage.preserves_terminal_promise
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    {world after : ActorWorld} {requester : ActorId}
    {receiver : EventualRef} {message : EventualMessage}
    {resultPromise promise : PromiseId} {history : List EventId}
    {state : PromiseState}
    (terminalLookup : world.promises promise = some state)
    (terminal : state.Terminal)
    (route : RouteEventualMessage isValue valueTransfer world requester receiver
      message resultPromise history after) :
    after.promises promise = some state := by
  induction route with
  | target target representation resultAfter =>
      rw [resultAfter]
      rw [ActorWorld.emitPacket_preserves_promises]
      rw [representation.preserves_promise_store transferPreserves]
      exact terminalLookup
  | @pending world requester owner routedPromise routedResult waiters routedMessage
      routedHistory pendingLookup =>
      by_cases same : promise = routedPromise
      · subst promise
        rw [terminalLookup] at pendingLookup
        have equal := Option.some.inj pendingLookup
        exact (terminal.not_pending equal).elim
      · simp [ActorWorld.registerPromiseWaiter, FiniteStore.install_away, same,
          terminalLookup]
  | @fulfilled world representedWorld after requester owner routedPromise
      routedResult result represented routedMessage routedHistory fulfilledLookup
      representation nested ih =>
      apply ih
      · rw [representation.preserves_promise_store transferPreserves]
        exact terminalLookup
  | @broken world representedWorld after requester owner routedPromise
      routedResult exception represented routedMessage routedHistory brokenLookup
      representation settlement =>
      have representedLookup : representedWorld.promises promise = some state := by
        rw [representation.preserves_promise_store transferPreserves]
        exact terminalLookup
      by_cases same : promise = routedResult
      · subst promise
        rcases settlement.requires_pending with ⟨pendingOwner, waiters, pending⟩
        rw [representedLookup] at pending
        have equal := Option.some.inj pending
        exact (terminal.not_pending equal).elim
      · rw [settlement.preserves_other_promise transferPreserves same]
        exact representedLookup

theorem ActorWorld.PromiseFrontierFresh.existing_ne_next
    {world : ActorWorld} (fresh : world.PromiseFrontierFresh)
    {promise : PromiseId} {state : PromiseState}
    (lookup : world.promises promise = some state) :
    promise ≠ ⟨world.nextPromise⟩ := by
  intro equal
  have member := world.promises.mem_domain_of_lookup_eq_some lookup
  have below := fresh promise member
  rw [equal] at below
  exact (Nat.lt_irrefl world.nextPromise below)

theorem AsynchronousSend.preserves_terminal_promise
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    {world after : ActorWorld} {actor : ActorId} {receiver : EventualRef}
    {message : EventualMessage} {history : List EventId}
    {resultPromise promise : PromiseId} {state : PromiseState}
    (fresh : world.PromiseFrontierFresh)
    (terminalLookup : world.promises promise = some state)
    (terminal : state.Terminal)
  (send : AsynchronousSend isValue valueTransfer world actor receiver message
      history after resultPromise) :
    after.promises promise = some state := by
  cases send with
  | send allocatedEqual route =>
      have different : promise ≠ ⟨world.nextPromise⟩ :=
        fresh.existing_ne_next terminalLookup
      have allocatedLookup :
          (world.allocatePendingPromise actor).1.promises promise = some state := by
        simp only [ActorWorld.allocatePendingPromise]
        rw [FiniteStore.install_away _ _ different]
        exact terminalLookup
      rw [allocatedEqual] at route
      exact route.preserves_terminal_promise transferPreserves allocatedLookup terminal

theorem ActorEventualSendStep.preserves_terminal_promise
    {interpretReference : LocalEventualReferenceInterpretation}
    {interpretMessage : LocalEventualMessageInterpretation}
    {installPromiseHandle : PromiseHandleInstallation}
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    {actor : ActorId} {before after : ActorWorld}
    {promise : PromiseId} {state : PromiseState}
    (fresh : before.PromiseFrontierFresh)
    (terminalLookup : before.promises promise = some state)
    (terminal : state.Terminal)
    (step : ActorEventualSendStep interpretReference interpretMessage
      installPromiseHandle isValue valueTransfer actor before after) :
    after.promises promise = some state := by
  cases step with
  | send run allocation control reference message send install =>
      simpa [ActorWorld.advanceRunningTurn] using
        send.preserves_terminal_promise transferPreserves fresh terminalLookup terminal

theorem ActorTurnCompletionStep.preserves_terminal_promise
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    {actor : ActorId} {before after : ActorWorld}
    {promise : PromiseId} {state : PromiseState}
    (terminalLookup : before.promises promise = some state)
    (terminal : state.Terminal)
  (step : ActorTurnCompletionStep isValue valueTransfer actor before after) :
    after.promises promise = some state := by
  cases step with
  | @«local» settled config reply triggering disposition value waiters run stack
      control pending settlement =>
      by_cases same : promise = reply
      · subst promise
        rw [terminalLookup] at pending
        have equal := Option.some.inj pending
        exact (terminal.not_pending equal).elim
      · simp only [ActorWorld.finishRunningTurn]
        rw [settlement.preserves_other_promise transferPreserves same]
        exact terminalLookup
  | remote run stack control pending different =>
      simp [ActorWorld.finishRunningTurn]
      exact terminalLookup

theorem SettlementPacketDequeueStep.preserves_terminal_promise
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    {actor : ActorId} {before after : ActorWorld}
    {promise : PromiseId} {state : PromiseState}
    (terminalLookup : before.promises promise = some state)
    (terminal : state.Terminal)
    (step : SettlementPacketDequeueStep isValue valueTransfer actor before after) :
    after.promises promise = some state := by
  cases step with
  | @dequeue consumed after packet remaining settledPromise disposition result
      idle mailbox payload consumedEqual settlement =>
      have consumedLookup : consumed.promises promise = some state := by
        rw [consumedEqual]
        exact terminalLookup
      by_cases same : promise = settledPromise
      · subst promise
        rcases settlement.requires_pending with ⟨owner, waiters, pending⟩
        rw [consumedLookup] at pending
        have equal := Option.some.inj pending
        exact (terminal.not_pending equal).elim
      · rw [settlement.preserves_other_promise transferPreserves same]
        exact consumedLookup

theorem WakePacketDequeueStep.preserves_terminal_promise
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    {actor : ActorId} {before after : ActorWorld}
    {promise : PromiseId} {state : PromiseState}
    (terminalLookup : before.promises promise = some state)
    (terminal : state.Terminal)
  (step : WakePacketDequeueStep isValue valueTransfer actor before after) :
    after.promises promise = some state := by
  cases step with
  | @fulfilled consumed representedWorld after packet remaining settledPromise
      resultPromise result represented message history idle mailbox payload
      consumedEqual representation route =>
      have consumedLookup : consumed.promises promise = some state := by
        rw [consumedEqual]
        exact terminalLookup
      have representedLookup : representedWorld.promises promise = some state := by
        rw [representation.preserves_promise_store transferPreserves]
        exact consumedLookup
      exact route.preserves_terminal_promise transferPreserves representedLookup terminal
  | @broken consumed after packet remaining settledPromise resultPromise result
      message history idle mailbox payload consumedEqual settlement =>
      have consumedLookup : consumed.promises promise = some state := by
        rw [consumedEqual]
        exact terminalLookup
      by_cases same : promise = resultPromise
      · subst promise
        rcases settlement.requires_pending with ⟨owner, waiters, pending⟩
        rw [consumedLookup] at pending
        have equal := Option.some.inj pending
        exact (terminal.not_pending equal).elim
      · rw [settlement.preserves_other_promise transferPreserves same]
        exact consumedLookup

theorem SelectedActorStep.preserves_terminal_promise
    {p : Program} {reifier : ErrorReifier p}
    {materialize : LocalMessageMaterialization}
    {interpretReference : LocalEventualReferenceInterpretation}
    {interpretMessage : LocalEventualMessageInterpretation}
    {installPromiseHandle : PromiseHandleInstallation}
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    {actor : ActorId} {before after : ActorWorld}
    {promise : PromiseId} {state : PromiseState}
    (fresh : before.PromiseFrontierFresh)
    (terminalLookup : before.promises promise = some state)
    (terminal : state.Terminal)
    (step : SelectedActorStep p reifier materialize interpretReference
      interpretMessage installPromiseHandle isValue valueTransfer actor before
      after) :
    after.promises promise = some state := by
  cases step with
  | start start =>
      cases start
      exact terminalLookup
  | sequential sequential =>
      cases sequential
      exact terminalLookup
  | eventual eventual =>
      exact eventual.preserves_terminal_promise transferPreserves fresh
        terminalLookup terminal
  | complete completion =>
      exact completion.preserves_terminal_promise transferPreserves
        terminalLookup terminal
  | settlement settlement =>
      exact settlement.preserves_terminal_promise transferPreserves
        terminalLookup terminal
  | wake wake =>
      exact wake.preserves_terminal_promise transferPreserves terminalLookup
        terminal

theorem ActorActionStep.preserves_terminal_promise
    {p : Program} {reifier : ErrorReifier p}
    {materialize : LocalMessageMaterialization}
    {interpretReference : LocalEventualReferenceInterpretation}
    {interpretMessage : LocalEventualMessageInterpretation}
    {installPromiseHandle : PromiseHandleInstallation}
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    {action : ActorAction} {before after : ActorWorld}
    {promise : PromiseId} {state : PromiseState}
    (fresh : before.PromiseFrontierFresh)
    (terminalLookup : before.promises promise = some state)
    (terminal : state.Terminal)
    (step : ActorActionStep p reifier materialize interpretReference
      interpretMessage installPromiseHandle isValue valueTransfer action before
      after) :
    after.promises promise = some state := by
  cases step with
  | compute selected =>
      exact selected.preserves_terminal_promise transferPreserves fresh
        terminalLookup terminal
  | deliver member eligible =>
      simpa using terminalLookup

theorem ActorSystemStep.preserves_terminal_promise
    {p : Program} {reifier : ErrorReifier p}
    {materialize : LocalMessageMaterialization}
    {interpretReference : LocalEventualReferenceInterpretation}
    {interpretMessage : LocalEventualMessageInterpretation}
    {installPromiseHandle : PromiseHandleInstallation}
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    {before after : ActorWorld} {promise : PromiseId} {state : PromiseState}
    (fresh : before.PromiseFrontierFresh)
    (terminalLookup : before.promises promise = some state)
    (terminal : state.Terminal)
    (step : ActorSystemStep p reifier materialize interpretReference
      interpretMessage installPromiseHandle isValue valueTransfer before after) :
    after.promises promise = some state := by
  rcases step with ⟨action, actionStep⟩
  exact actionStep.preserves_terminal_promise transferPreserves fresh
    terminalLookup terminal

/-- A visible pending-to-terminal change of one promise between consecutive
    worlds.  This definition deliberately abstracts over whether settlement
    arose from turn completion, a settlement packet, or propagation of a
    broken promise. -/
def PromiseSettlementTransition (execution : Nat → ActorWorld)
    (promise : PromiseId) (index : Nat) : Prop :=
  (∃ owner waiters,
      (execution index).promises promise = some (.pending owner waiters)) ∧
    PromiseTerminalAt (execution (index + 1)) promise

theorem IsActorExecution.terminal_promise_persists
    {p : Program} {reifier : ErrorReifier p}
    {materialize : LocalMessageMaterialization}
    {interpretReference : LocalEventualReferenceInterpretation}
    {interpretMessage : LocalEventualMessageInterpretation}
    {installPromiseHandle : PromiseHandleInstallation}
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    {execution : Nat → ActorWorld}
    (run : IsActorExecution p reifier materialize interpretReference
      interpretMessage installPromiseHandle isValue valueTransfer execution)
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    (frontiers : ∀ index, (execution index).PromiseFrontierFresh)
    {promise : PromiseId} {state : PromiseState} {origin later : Nat}
    (atOrigin : (execution origin).promises promise = some state)
    (terminal : state.Terminal) (notEarlier : origin ≤ later) :
    (execution later).promises promise = some state := by
  induction later with
  | zero =>
      have atZero : origin = 0 := Nat.eq_zero_of_le_zero notEarlier
      subst origin
      exact atOrigin
  | succ index ih =>
      by_cases atOriginIndex : origin = index + 1
      · subst origin
        exact atOrigin
      · have originBeforeIndex : origin ≤ index :=
          Nat.le_of_lt_succ (Nat.lt_of_le_of_ne notEarlier atOriginIndex)
        exact (run index).preserves_terminal_promise transferPreserves
          (frontiers index) (ih originBeforeIndex) terminal

theorem IsActorExecution.promise_settles_at_most_once
    {p : Program} {reifier : ErrorReifier p}
    {materialize : LocalMessageMaterialization}
    {interpretReference : LocalEventualReferenceInterpretation}
    {interpretMessage : LocalEventualMessageInterpretation}
    {installPromiseHandle : PromiseHandleInstallation}
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation}
    {execution : Nat → ActorWorld}
    (run : IsActorExecution p reifier materialize interpretReference
      interpretMessage installPromiseHandle isValue valueTransfer execution)
    (transferPreserves : ValueTransferPreservesPromiseStore valueTransfer)
    (frontiers : ∀ index, (execution index).PromiseFrontierFresh)
    {promise : PromiseId} {first second : Nat}
    (firstSettlement : PromiseSettlementTransition execution promise first)
    (secondSettlement : PromiseSettlementTransition execution promise second) :
    first = second := by
  rcases firstSettlement with ⟨firstPending, firstTerminal⟩
  rcases secondSettlement with ⟨secondPending, secondTerminal⟩
  rcases firstTerminal with ⟨firstState, firstLookup, firstIsTerminal⟩
  rcases secondTerminal with ⟨secondState, secondLookup, secondIsTerminal⟩
  rcases Nat.lt_trichotomy first second with before | same | after
  · rcases secondPending with ⟨owner, waiters, pending⟩
    have persistent := run.terminal_promise_persists transferPreserves frontiers
      firstLookup firstIsTerminal (Nat.succ_le_of_lt before)
    rw [persistent] at pending
    have equal := Option.some.inj pending
    exact (firstIsTerminal.not_pending equal).elim
  · exact same
  · rcases firstPending with ⟨owner, waiters, pending⟩
    have persistent := run.terminal_promise_persists transferPreserves frontiers
      secondLookup secondIsTerminal (Nat.succ_le_of_lt after)
    rw [persistent] at pending
    have equal := Option.some.inj pending
    exact (secondIsTerminal.not_pending equal).elim

/-- The recursive wake emitter is instrumented propositionally: at every
    recursive emission point the originating promise is already terminal.
    This is stronger than checking only the final world and records the
    commit-before-notification order used by the operational definition. -/
def WakeEmissionSourcesTerminal (world : ActorWorld) (owner : ActorId)
    (settledPromise : PromiseId) (disposition : SettlementDisposition)
    (result : EventualRef) : List PromiseWaiter → Prop
  | [] => PromiseTerminalAt world settledPromise
  | waiter :: remaining =>
      PromiseTerminalAt world settledPromise ∧
        WakeEmissionSourcesTerminal
          (world.emitPacket owner waiter.actor
            (.wake settledPromise waiter.resultPromise disposition result
              waiter.message waiter.causalHistory))
          owner settledPromise disposition result remaining

theorem WakeEmissionSourcesTerminal.of_terminal
    {world : ActorWorld} {owner : ActorId} {settledPromise : PromiseId}
    {disposition : SettlementDisposition} {result : EventualRef}
    (terminal : PromiseTerminalAt world settledPromise)
    (waiters : List PromiseWaiter) :
    WakeEmissionSourcesTerminal world owner settledPromise disposition result
      waiters := by
  induction waiters generalizing world with
  | nil => exact terminal
  | cons waiter remaining ih =>
      refine ⟨terminal, ih ?_⟩
      rcases terminal with ⟨state, lookup, isTerminal⟩
      exact ⟨state, by simpa using lookup, isTerminal⟩

theorem PromiseSettlement.emits_wakes_only_after_terminal_commit
    {isValue : ActorWorld → ActorId → ObjRef → Prop}
    {valueTransfer : ValueTransferRelation} {world after : ActorWorld}
    {promise : PromiseId} {disposition : SettlementDisposition}
    {source : ActorId} {result : EventualRef} {history : List EventId}
    (settlement : PromiseSettlement isValue valueTransfer world promise
      disposition source result history after) :
    ∃ (owner : ActorId) (represented : EventualRef)
        (waiters : List PromiseWaiter) (representedWorld : ActorWorld),
      WakeEmissionSourcesTerminal
        { representedWorld with
          promises := representedWorld.promises.install promise
            (match disposition with
              | .fulfilled => .fulfilled owner represented
              | .broken => .broken owner represented) }
        owner promise disposition represented waiters := by
  cases settlement with
  | @settle world representedWorld after owner source waiters disposition result
      represented history pending subset representation resultAfter =>
      refine ⟨owner, represented, waiters, world, ?_⟩
      apply WakeEmissionSourcesTerminal.of_terminal
      cases disposition
      · exact ⟨.fulfilled owner represented, by simp, trivial⟩
      · exact ⟨.broken owner represented, by simp, trivial⟩

end Newspeak
