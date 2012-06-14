Object subclass: #Method
	instanceVariableNames: 'outIndex block '
	classVariableNames: ''
	poolDictionaries: ''
	category: 'DB-DeltaBlue'!
Method comment:
'I represent a method whose enforement procedure is stored in a Smalltalk block. Users may create custom methods by supplying an assignment expression string and a set of formal constrained variable names. See my instance creation protocol for further details.

Instance variables:
	outIndex		the index of my output variable (target of the assignment) in my constraint
	block		block to execute to enforce the constraint <BlockContext>
'!


!Method methodsFor: 'initialize-release'!

names: variableNames methodString: methodString
	"Initialize a method by compiling the given string considering the given collection of variable names to represent the parameters of the method (i.e. its inputs and outputs). A given variable may not be both an input and an output. Note: Any free variables in the methodString will be considered global (if they appear in 'Smalltalk') or temporary variables. The user is given a warning, however, since such cases are unusual and a free variable may indicate a typographical error."

	| insOutsTemps ins outs temps |
	insOutsTemps _ self extractInsOutsAndTemps: methodString using: variableNames.
	ins _ insOutsTemps at: 1.
	outs _ insOutsTemps at: 2.
	temps _ insOutsTemps at: 3.
	outIndex _ self outIndexForIns: ins outs: outs temps: temps all: variableNames.
	block _ Compiler
			evaluate:
				((self blockPrefixForIns: ins temps: temps args: variableNames),
				 methodString,
				 (self blockPostfixForOuts: outs allNames: variableNames))
			for: nil
			logged: false.
	(temps size > 0) ifTrue: [block fixTemps].!

release

	outIndex _ nil.
	block _ nil.! !

!Method methodsFor: 'constraint support'!

execute: variables
	"Execute myself to enforce my constraint on the given variables."

	block value: variables.!

outIndex
	"Answer the index of my output in the bindings array."

	^outIndex! !

!Method methodsFor: 'printing'!

printOn: aStream

	aStream
		nextPutAll: 'Method(', self asOop printString;
		nextPutAll: ' out: ', outIndex printString, ')'.! !

!Method methodsFor: 'private'!

blockPostfixForOuts: outNames allNames: allNames
	"Answer a string to be used as the postfix when creating a block for this method."

	| stream |
	"make a stream and add separator to terminate user's method string"
	stream _ WriteStream on: (String new).
	stream nextPutAll: '.'; cr.

	"build the expression postfix, creating assignments for all outputs"
	1 to: allNames size do:
		[: index |
		 (outNames includes: (allNames at: index)) ifTrue:
			[stream tab; nextPutAll: '(vars at: '.
			 stream nextPutAll: index printString, ') value: '.
			 stream nextPutAll: (allNames at: index), '.'; cr]].

	stream tab; nextPutAll: ']'; cr.
	^stream contents!

blockPrefixForIns: inNames temps: tempNames args: argNames
	"Answer a string to be used as the prefix when creating a block for a method with the given input names. All constraint variables are declared as temporaries, in addition to the temporary variables from the method string. Input variable temporaries are initialized from the argument vector."

	| stream |
	stream _ WriteStream on: (String new).

	"build the expression prefix, making all the variables look like temps"
	stream nextPutAll: '| '.
	argNames do: [: v | stream nextPutAll: v; space].
	tempNames do: [: v | stream nextPutAll: v; space].
	stream nextPutAll: '|'; cr.

	"build the block header and input assignments"
	stream tab; nextPutAll: '[: vars |'; cr.
	1 to: argNames size do:
		[: index |
		 (inNames includes: (argNames at: index)) ifTrue:
			[stream tab; nextPutAll: (argNames at: index), ' _ (vars at: '.
			stream nextPutAll: index printString.
			stream nextPutAll: ') value.'; cr]].

	stream tab.
	^stream contents!

extractInsOutsAndTemps: methodString using: allNames
	"Extract the input, output and temporary variable names from the Smalltalk expression represented by the given string. A temporary variable is one that is neither an input, an output, or a global. Answer an array containing the three lists (ins, outs, temps)."

	| s parseTree ins outs temps |
	s _ (String new: 200) writeStream.
	s nextPutAll: 'DoIt'; cr; cr.
	s tab; nextPutAll: '| '.
	allNames do: [: vName | s nextPutAll: vName; space].
	s nextPutAll: '|'; cr; tab; nextPutAll: methodString.
	parseTree _ self parse: s contents.
	ins _ parseTree referenced.
	outs _ parseTree assignedTo.
	temps _ parseTree allVariables select:
		[: v | ((allNames includes: v) not) &
			  ((Smalltalk includesKey: v) not)].
	^Array with: ins with: outs with: temps!

outIndexForIns: inNames outs: outNames temps: tempNames all: allNames
	"Answer the index of the method output in the constraint variables. Raise an error if the input and output arg lists are not disjoint or if there is not exactly one output. Warn the user if the method code has free variables (these will be made into temporaries)."

	| realOuts |
	realOuts _ outNames copy removeAll: tempNames; yourself.
	(realOuts size = 1) ifFalse:
		[self error: 'Constraints must have exactly one output variable'].

	outNames do:
		[: v |
		 ((inNames includes: v) and:
		  [allNames includes: v]) ifTrue:
			[self error: v asString, ' cannot be both input and output!!']].

	tempNames do:
		[: v |
		 Transcript show:
			'Warning: ''', v, ''' is assumed to be a temporary.'; cr].

	^allNames indexOf: (realOuts asOrderedCollection first)!

parse: methodString
	"Answer the Smalltalk parse tree for the given string."

	^(Compiler new)
		parse: methodString readStream
		in: UndefinedObject
		notifying: nil! !
"-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- "!

Method class
	instanceVariableNames: ''!


!Method class methodsFor: 'instance creation'!

names: variableNames methodString: methodString
	"Create a constraint method from the given string, an assignment statement using the given variable names. For example:

		Method names: #(a b c) methodString: 'a _ b * c'"

	^(super new)
		names: variableNames
		methodString: methodString! !

Object subclass: #Strength
	instanceVariableNames: 'symbolicValue arithmeticValue '
	classVariableNames: 'AbsoluteStrongest AbsoluteWeakest Required StrengthConstants StrengthTable '
	poolDictionaries: ''
	category: 'DB-DeltaBlue'!
Strength comment:
'Strengths are used to measure the relative importance of constraints. The hierarchy of available strengths is determined by the class variable StrengthTable (see my class initialization method). Because Strengths are invariant, references to Strength instances are shared (i.e. all references to "Strength of: #required" point to a single, shared instance). New strengths may be inserted in the strength hierarchy without disrupting current constraints.

Instance variables:
	symbolicValue		symbolic strength name (e.g. #required) <Symbol>
	arithmeticValue		index of the constraint in the hierarchy, used for comparisons <Number>
'!


!Strength methodsFor: 'comparing'!

sameAs: aStrength
	"Answer true if I am the same strength as the given Strength."

	^arithmeticValue = aStrength arithmeticValue!

stronger: aStrength
	"Answer true if I am stronger than the given Strength."

	^arithmeticValue < aStrength arithmeticValue!

weaker: aStrength
	"Answer true if I am weaker than the given Strength."

	^arithmeticValue > aStrength arithmeticValue! !

!Strength methodsFor: 'max/min'!

strongest: aStrength
	"Answer the stronger of myself and aStrength."

	(aStrength stronger: self)
		ifTrue: [^aStrength]
		ifFalse: [^self].!

weakest: aStrength
	"Answer the weaker of myself and aStrength."

	(aStrength weaker: self)
		ifTrue: [^aStrength]
		ifFalse: [^self].! !

!Strength methodsFor: 'printing'!

printOn: aStream
	"Append a string which represents my strength onto aStream."

	aStream nextPutAll: '%', symbolicValue, '%'.! !

!Strength methodsFor: 'private'!

arithmeticValue
	"Answer my arithmetic value. Used for comparisons. Note that STRONGER constraints have SMALLER arithmetic values."

	^arithmeticValue!

initializeWith: symVal
	"Record my symbolic value and reset my arithmetic value."

	symbolicValue _ symVal.
	self resetValue.!

resetValue
	"Lookup my symbolic value in the StrengthTable and reset my internal value."

	arithmeticValue _ StrengthTable at: symbolicValue.! !
"-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- "!

Strength class
	instanceVariableNames: ''!


!Strength class methodsFor: 'class initialization'!

initialize
	"Initialize the symbolic strength table. Fix the internally caches values of all existing instances."
	"Strength initialize"

	StrengthTable _ Dictionary new.
	StrengthTable at: #absoluteStrongest put: -1000.
	StrengthTable at: #required put: 0.
	StrengthTable at: #strongPreferred put: 1.
	StrengthTable at: #preferred put: 2.
	StrengthTable at: #strongDefault put: 3.
	StrengthTable at: #default put: 4.
	StrengthTable at: #weakDefault put: 5.
	StrengthTable at: #absoluteWeakest put: 1000.

	StrengthConstants _ Dictionary new.
	StrengthTable keys do:
		[: strengthSymbol |
			StrengthConstants
				at: strengthSymbol
				put: ((super new) initializeWith: strengthSymbol)].

	"Fix arithmetic values stored in all instances."
	Strength allInstancesDo:
		[: strength | strength resetValue].

	AbsoluteStrongest _ Strength of: #absoluteStrongest.
	AbsoluteWeakest _ Strength of: #absoluteWeakest.
	Required _ Strength of: #required.! !

!Strength class methodsFor: 'instance creation'!

of: aSymbol
	"Answer an instance with the specified strength."

	^StrengthConstants at: aSymbol! !

!Strength class methodsFor: 'constants'!

absoluteStrongest

	^AbsoluteStrongest!

absoluteWeakest

	^AbsoluteWeakest!

required

	^Required! !

Strength initialize!


OrderedCollection variableSubclass: #Plan
	instanceVariableNames: ''
	classVariableNames: ''
	poolDictionaries: ''
	category: 'DB-DeltaBlue'!
Plan comment:
'A Plan is an ordered list of constraints to be executed in sequence to resatisfy all currently satisfiable constraints in the face of one or more changing inputs.'!


!Plan methodsFor: 'execution'!

execute
	"Execute my constraints in order."

	self do: [: c | c execute].! !

Object subclass: #Planner
	instanceVariableNames: ''
	classVariableNames: ''
	poolDictionaries: ''
	category: 'DB-DeltaBlue'!
Planner comment:
'I embody the DeltaBlue algorithm described in:
	"The DeltaBlue Algorithm: An Incremental Constraint Hierarchy Solver"
	by Bjorn N. Freeman-Benson and John Maloney
See January 1990 Communications of the ACM or University of Washington TR 89-08-06 for further details.'!

"-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- "!

Planner class
	instanceVariableNames: 'currentMark '!


!Planner class methodsFor: 'class initialization'!

initialize
	"Planner initialize"

	currentMark _ 1.! !

!Planner class methodsFor: 'add/remove'!

incrementalAdd: c
	"Attempt to satisfy the given constraint and, if successful, incrementally update the dataflow graph."
	"Details: If satifying the constraint is successful, it may override a weaker constraint on its output. The algorithm attempts to resatisfy that constraint using some other method. This process is repeated until either a) it reaches a variable that was not previously determined by any constraint or b) it reaches a constraint that is too weak to be satisfied using any of its methods. The variables of constraints that have been processed are marked with a unique mark value so that we know where we've been. This allows the algorithm to avoid getting into an infinite loop even if the constraint graph has an inadvertent cycle."

	| mark overridden |
	mark _ self newMark.
	overridden _ c satisfy: mark.
	[overridden == nil] whileFalse:
		[overridden _ overridden satisfy: mark].!

incrementalRemove: c
	"Entry point for retracting a constraint. Remove the given constraint and incrementally update the dataflow graph."
	"Details: Retracting the given constraint may allow some currently unsatisfiable downstream constraint be satisfied. We thus collect a list of unsatisfied downstream constraints and attempt to satisfy each one in turn. This list is sorted by constraint strength, strongest first, as a heuristic for avoiding unnecessarily adding and then overriding weak constraints."
	"Assume: c is satisfied."

	| out unsatisfied |
	out _ c output.
	c markUnsatisfied.
	c removeFromGraph.
	unsatisfied _ self removePropagateFrom: out.
	unsatisfied do: [: u | self incrementalAdd: u].! !

!Planner class methodsFor: 'planning/value propagation'!

extractPlanFromConstraints: constraints
	"Extract a plan for resatisfaction starting from the outputs of the given constraints, usually a set of input constraints."

	| sources |
	sources _ OrderedCollection new.
	constraints do:
		[: c | ((c isInput) and: [c isSatisfied]) ifTrue: [sources add: c]].
	^self makePlan: sources!

extractPlanFromVariables: variables
	"Extract a plan from the dataflow graph having the given variables. It is assumed that the given set of variables is complete, or at least that it contains all the input variables."

	| sources |
	sources _ OrderedCollection new.
	variables do:
		[: v |
		 (v constraints) do:
			[: c | ((c isInput) and: [c isSatisfied]) ifTrue: [sources add: c]]].
	^self makePlan: sources!

makePlan: sources
	"Extract a plan for resatisfaction starting from the given source constraints, usually a set of input constraints. This method assumes that stay optimization is desired; the plan will contain only constraints whose output variables are not stay. Constraints that do no computation, such as stay and edit constraints, are not included in the plan."
	"Details: The outputs of a constraint are marked when it is added to the plan under construction. A constraint may be appended to the plan when all its input variables are known. A variable is known if either a) the variable is marked (indicating that has been computed by a constraint appearing earlier in the plan), b) the variable is 'stay' (i.e. it is a constant at plan execution time), or c) the variable is not determined by any constraint. The last provision is for past states of history variables, which are not stay but which are also not computed by any constraint."
	"Assume: sources are all satisfied."

	| mark plan todo c |
	mark _ self newMark.
	plan _ Plan new.
	todo _ sources.
	[todo isEmpty] whileFalse:
		[c _ todo removeFirst.
		 ((c output mark ~= mark) and:		"not in plan already and..."
		  [c inputsKnown: mark]) ifTrue:		"eligible for inclusion"
			[plan addLast: c.
			 c output mark: mark.
			 c _ self addConstraintsConsuming: c output to: todo]].
	^plan!

propagateFrom: v
	"The given variable has changed. Propagate new values downstream."

	| todo c |
	todo _ OrderedCollection new.
	self addConstraintsConsuming: v to: todo.
	[todo isEmpty] whileFalse:
		[c _ todo removeFirst.
		 c execute.
		 self addConstraintsConsuming: c output to: todo].! !

!Planner class methodsFor: 'benchmarks'!

chainTest: n
	"Do chain-of-equality-constraints performance tests, printing the results in the Transcript."
	"Planner chainTest: 100"

	| equalsC vars constraints v1 v2 eqC editConstraint plan |
	"This constraint is slower than the special-purpose EqualityConstraint."
	equalsC _ Constraint
		names: #(a b)
		methods: #('a _ b'   'b _ a').

	self report: 'Built chain of ', n printString, ' equality constraints in' times: 1 run:
		[vars _ (0 to: n) collect: [: i | Variable new].
		 constraints _ OrderedCollection new: n.
		 "thread a chain of equality constraints through the variables"
		 1 to: n do:
			[: i |
			 v1 _ (vars at: i).
			 v2 _ (vars at: i + 1).
			 eqC _ v1 requireEquals: v2 "equalsC copy var: v1 var: v2 strength: #required".
			 constraints add: eqC].
		 vars last strongDefaultStay].

	self report: 'Add constraint (case 1):' times: 1 run:
		[editConstraint _ EditConstraint var: (vars first) strength: #preferred].
	self report: 'Make Plan (case 1)' times: 1 run:
		[plan _ Planner extractPlanFromConstraints: (Array with: editConstraint)].
	Transcript show: 'Plan length: ', plan size printString, ' constraints'; cr.
	self report: 'Execute Plan (case 1):' times: 20 run:
		[plan execute].
	self report: 'Remove constraint (case 1):' times: 1 run:
		[editConstraint destroyConstraint].
	self report: 'Setting first node: (case 1a):' times: 1 run:
		[(vars first) setValue: 123 strength: #strongPreferred].
	self report: 'Setting last node: (case 1b):' times: 1 run:
		[(vars last) setValue: 321 strength: #strongPreferred].
	Transcript cr.

	self report: 'Add constraint (case 2):' times: 1 run:
		[editConstraint _ EditConstraint var: (vars first) strength: #default].
	self report: 'Make Plan (case 2):' times: 1 run:
		[plan _ Planner extractPlanFromConstraints: (Array with: editConstraint)].
	Transcript show: 'Plan length: ', plan size printString, ' constraints'; cr.
	self report: 'Execute Plan (case 2):' times: 20 run:
		[plan execute].
	self report: 'Remove constraint (case 2):' times: 1 run:
		[editConstraint destroyConstraint].
	self report: 'Setting first node: (case 2a):' times: 1 run:
		[(vars first) setValue: 1230 strength: #weakDefault].
	self report: 'Setting last node: (case 2b):' times: 1 run:
		[(vars last) setValue: 3210 strength: #weakDefault].
	Transcript cr.

	constraints do: [: c | c release].
	vars do: [: v | v release].
	Transcript cr.!

projectionTest: n
"This test constructs a two sets of variables related to each other by a simple linear transformation (scale and offset). The time is measured to change a variable on either side of the mapping and to change the scale and offset factors. Results are printed in the Transcript."
	"Planner projectionTest: 100"

	| projectionC constraints scale offset src dst |
	"This constraint is slower than the special-purpose ScaleConstraint."
	projectionC _ Constraint
		names: #(src scale offset dst)
		methods: #('dst _ (src * scale) + offset'   'src _ (dst - offset) // scale').
	constraints _ OrderedCollection new.

	self report: 'Projection test for ', n printString, ' points (Smalltalk):' times: 1 run:
		[scale _ Variable value: 10.
		 offset _ Variable value: 1000.
		 1 to: n do:
			[: i |
			 src _ Variable value: i.
			 dst _ Variable value: i.
			 constraints add: (src defaultStay).
			 constraints add:
				("(projectionC copy)"ScaleConstraint
					var: src var: scale var: offset var: dst
					strength: #required)]].
	self reportChange: 'Changing a data point:'
		var: src newValue: 17.
	self reportChange: 'Changing a projected point:'
		var: dst newValue: 1050.
	self reportChange: 'Changing the scale factor:'
		var: scale newValue: 5.
	self reportChange: 'Changing the offset:'
		var: offset newValue: 2000.

	constraints do: [: c | c release].
	Transcript cr.!

report: string times: count run: aBlock
	"Report the time required to execute the given block."

	| time |
	time _ Time millisecondsToRun: [count timesRepeat: aBlock].
	Transcript show: string, ' ', (time // count) printString, ' milliseconds'; cr.!

reportChange: title var: aVariable newValue: newValue

	| editConstraint plan |
	Transcript show: title; cr.
	self report: '  Adding Constraint:' times: 1 run:
		[editConstraint _ EditConstraint var: aVariable strength: #preferred].
	self report: '  Making Plan' times: 1 run:
		[plan _ Planner extractPlanFromConstraints: (Array with: editConstraint)].
	Transcript show: '  Plan size: ', plan size printString, ' constraints'; cr.
	self report: '  Executing Plan:' times: 10 run:
		[aVariable value: newValue. plan execute].
	self report: '  Removing Constraint:' times: 1 run:
		[editConstraint destroyConstraint].! !

!Planner class methodsFor: 'private'!

addConstraintsConsuming: v to: aCollection

	| determiningC |
	determiningC _ v determinedBy.
	v constraints do:
		[: c |
		 ((c == determiningC) or: [c isSatisfied not]) ifFalse:
			[aCollection add: c]].!

addPropagate: c mark: mark
	"Recompute the walkabout strengths and stay flags of all variables downstream of the given constraint and recompute the actual values of all variables whose stay flag is true. If a cycle is detected, remove the given constraint and answer false. Otherwise, answer true."
	"Details: Cycles are detected when a marked variable is encountered downstream of the given constraint. The sender is assumed to have marked the inputs of the given constraint with the given mark. Thus, encountering a marked node downstream of the output constraint means that there is a path from the constraint's output to one of its inputs."

	| todo d |
	todo _ OrderedCollection with: c.
	[todo isEmpty] whileFalse:
		[d _ todo removeFirst.
		 (d output mark = mark) ifTrue:
			[self incrementalRemove: c.
			 ^false].
		 d recalculate.
		 self addConstraintsConsuming: d output to: todo].
	^true!

constraintsConsuming: v do: aBlock

	| determiningC |
	determiningC _ v determinedBy.
	v constraints do:
		[: c |
		 ((c == determiningC) or: [c isSatisfied not]) ifFalse:
			[aBlock value: c]].!

newMark
	"Select a previously unused mark value."
	"Details: We just keep incrementing. If necessary, the counter will turn into a LargePositiveInteger. In that case, it will be a bit slower to compute the next mark but the algorithms will all behave correctly. We reserve the value '0' to mean 'unmarked'. Thus, this generator starts at '1' and will never produce '0' as a mark value."

	^currentMark _ currentMark + 1!

removePropagateFrom: out
	"Update the walkabout strengths and stay flags of all variables downstream of the given constraint. Answer a collection of unsatisfied constraints sorted in order of decreasing strength."

	| unsatisfied todo v nextC |
	unsatisfied _ SortedCollection sortBlock:
		[: c1 : c2 | c1 strength stronger: c2 strength].
	out determinedBy: nil.
	out walkStrength: Strength absoluteWeakest.
	out stay: true.
	todo _ OrderedCollection with: out.
	[todo isEmpty] whileFalse:
		[v _ todo removeFirst.
		 v constraints do:
		 	[: c | (c isSatisfied) ifFalse: [unsatisfied add: c]].
		 self constraintsConsuming: v do:
			[: c |
			 c recalculate.
			 todo add: c output]].
	^unsatisfied! !

Planner initialize!


Object subclass: #Variable
	instanceVariableNames: 'value constraints determinedBy walkStrength stay mark '
	classVariableNames: ''
	poolDictionaries: ''
	category: 'DB-DeltaBlue'!
Variable comment:
'I represent a constrained variable. In addition to my value, I maintain the structure of the constraint graph, the current dataflow graph, and various parameters of interest to the DeltaBlue incremental constraint solver.

Instance variables:
	value			my value; changed by constraints, read by client <Object>
	constraints		normal constraints that reference me <Array of Constraint>
	determinedBy	the constraint that currently determines
					my value (or nil if there isn''t one) <Constraint>
	walkStrength		my walkabout strength <Strength>
	stay			true if I am a planning-time constant <Boolean>
	mark			used by the planner to mark constraints <Number>'!


!Variable methodsFor: 'initialize-release'!

initialize

	value _ 0.
	constraints _ OrderedCollection new: 2.
	determinedBy _ nil.
	walkStrength _ Strength absoluteWeakest.
	stay _ true.
	mark _ 0.!

release
	"Break cycles (but leave me printable)."

	self initialize.! !

!Variable methodsFor: 'access'!

addConstraint: aConstraint
	"Add the given constraint to the set of all constraints that refer to me."

	constraints add: aConstraint.!

constraints
	"Answer the set of constraints that refer to me."

	^constraints!

determinedBy
	"Answer the constraint that determines my value in the current dataflow."

	^determinedBy!

determinedBy: aConstraint
	"Record that the given constraint determines my value in the current data flow."

	determinedBy _ aConstraint.!

mark
	"Answer my mark value."

	^mark!

mark: markValue
	"Set my mark value."

	mark _ markValue.!

removeConstraint: c
	"Remove all traces of c from this variable."

	constraints remove: c ifAbsent: [].
	(determinedBy == c) ifTrue: [determinedBy _ nil].!

stay
	"Answer my stay flag."

	^stay!

stay: aBoolean
	"Set my stay flag."

	stay _ aBoolean!

value
	"Answer my value."

	^value!

value: anObject
	"Set my value."

	value _ anObject.!

walkStrength
	"Answer my walkabout strength in the current dataflow."

	^walkStrength!

walkStrength: aStrength
	"Set my walkabout strength in the current dataflow."

	walkStrength _ aStrength.! !

!Variable methodsFor: 'changes'!

changeIn: aBlock strength: strengthSymbol
	"Attempt to add an edit constraint of the given strength to myself and execute the given block only if this constraint can be satisfied (i.e. no stronger constraint prevents me from changing)."

	| editConstraint |
	editConstraint _ EditConstraint var: self strength: strengthSymbol.
	(editConstraint isSatisfied) ifTrue:
		[aBlock value.
		 Planner propagateFrom: self].
	editConstraint destroyConstraint.!

setAll: variables to: values strength: strengthSymbol
	"Attempt to assign the given values to the given variables using the given strength. This is an all-or-nothing operation; if any variable cannot be changed due to a stronger constraint then no variable is changed."

	| allSatisfied editConstraints editConstraint |
	(variables size = values size) ifFalse:
		[^self error: 'variable and value lists must be same size'].

	"add edit constraints"
	allSatisfied _ true.		"true iff all edit constraints are satisfied"
	editConstraints _ variables collect:
		[: v |
		 editConstraint _ EditConstraint var: v strength: strengthSymbol.
		 (editConstraint isSatisfied) ifFalse: [allSatisfied _ false].
		 editConstraint].

	(allSatisfied) ifTrue:
		["do the assignments only if all edit constraints are satisfied"
		 variables with: values do:
			[: thisVar : thisValue |
			 thisVar value: thisValue.
			 Planner propagateFrom: thisVar]].

	"remove edit constraints"
	editConstraints do: [: c | c destroyConstraint].!

setValue: aValue
	"Attempt to assign the given value to me using a strength of #preferred."

	self setValue: aValue strength: #preferred.!

setValue: aValue strength: strengthSymbol
	"Attempt to assign the given value to me using the given strength."

	| editConstraint |
	editConstraint _ EditConstraint var: self strength: strengthSymbol.
	(editConstraint isSatisfied) ifTrue:
		[self value: aValue.
		 Planner propagateFrom: self].
	editConstraint destroyConstraint.! !

!Variable methodsFor: 'stay constraints'!

defaultStay

	^StayConstraint var: self strength: #default!

preferredStay

	^StayConstraint var: self strength: #preferred!

requiredStay

	^StayConstraint var: self strength: #required!

strongDefaultStay

	^StayConstraint var: self strength: #strongDefault!

strongPreferredStay

	^StayConstraint var: self strength: #strongPreferred!

weakDefaultStay

	^StayConstraint var: self strength: #weakDefault! !

!Variable methodsFor: 'equality constraints'!

requireEquals: aVariable
	"Install a required equality constraint between me and the given variable."

	^EqualityConstraint var: self var: aVariable strength: #required! !

!Variable methodsFor: 'printing'!

longPrintOn: aStream

	self shortPrintOn: aStream.
	aStream nextPutAll: '   Constraints: '.
	(constraints isEmpty)
		ifTrue: [aStream cr; tab; nextPutAll: 'none']
		ifFalse:
			[constraints do:
				[: c | aStream cr; tab. c shortPrintOn: aStream]].
	(determinedBy isNil) ifFalse:
		[aStream cr; nextPutAll: '   Determined by: '.
		 aStream cr; tab. determinedBy shortPrintOn: aStream].
	aStream cr.!

printOn: aStream

	(Sensor leftShiftDown)
		ifTrue: [self longPrintOn: aStream]
		ifFalse: [self shortPrintOn: aStream].!

shortPrintOn: aStream

	aStream nextPutAll: 'V(', self asOop printString, ', '.
	aStream nextPutAll: walkStrength printString, ', '.
	(stay isNil) ifFalse:
		[aStream nextPutAll: (stay ifTrue: ['stay, '] ifFalse: ['changing, '])].
	aStream nextPutAll: value printString.
	aStream nextPutAll: ')'.
	aStream cr.! !
"-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- "!

Variable class
	instanceVariableNames: ''!


!Variable class methodsFor: 'instance creation'!

new

	^super new initialize!

value: aValue

	^(super new) initialize; value: aValue! !

Object subclass: #AbstractConstraint
	instanceVariableNames: 'strength '
	classVariableNames: ''
	poolDictionaries: ''
	category: 'DB-DeltaBlue'!
AbstractConstraint comment:
'I am an abstract class representing a system-maintainable relationship (or "constraint") between a set of variables. I supply a strength instance variable; concrete subclasses provide a means of storing the constrained variables and other information required to represent a constraint.

Instance variables:
	strength			the strength of this constraint <Strength>
'!


!AbstractConstraint methodsFor: 'accessing'!

strength
	"Answer my strength."

	^strength!

strength: strengthSymbol
	"Set my strength."

	strength _ Strength of: strengthSymbol.! !

!AbstractConstraint methodsFor: 'queries'!

includeInPlan
	"Answer true if this constraint should be included in the plan. Subclasses such as EditConstraint and StayConstraint override this method to return 'false', since they are noops at plan execution time."

	^true!

isInput
	"Normal constraints are not input constraints. An input constraint is one that depends on external state, such as the mouse, the keyboard, a clock, or some arbitrary piece of imperative code."

	^false!

isSatisfied
	"Answer true if this constraint is satisfied in the current solution."

	self subclassResponsibility! !

!AbstractConstraint methodsFor: 'add/remove'!

addConstraint
	"Activate this constraint and attempt to satisfy it."

	self addToGraph.
	Planner incrementalAdd: self.!

addToGraph
	"Add myself to the constraint graph."

	self subclassResponsibility!

destroyConstraint
	"Deactivate this constraint, remove it from the constraint graph, possibly causing other constraints to be satisfied, and destroy it."

	(self isSatisfied) ifTrue: [Planner incrementalRemove: self].
	self removeFromGraph.
	self release.!

removeFromGraph
	"Remove myself from the constraint graph."

	self subclassResponsibility! !

!AbstractConstraint methodsFor: 'planning'!

chooseMethod: mark
	"Decide if I can be satisfied and record that decision. The output of the choosen method must not have the given mark and must have a walkabout strength less than that of this constraint."

	self subclassResponsibility!

execute
	"Enforce this constraint. Assume that it is satisfied."

	self subclassResponsibility!

inputsDo: aBlock
	"Assume that I am satisfied. Evaluate the given block on all my current input variables."

	self subclassResponsibility!

inputsKnown: mark
	"Assume that I am satisfied. Answer true if all my current inputs are known. A variable is known if either a) it is 'stay' (i.e. it is a constant at plan execution time), b) it has the given mark (indicating that it has been computed by a constraint appearing earlier in the plan), or c) it is not determined by any constraint."

	self inputsDo:
		[: v |
		 ((v mark = mark) or: [(v stay) or: [v determinedBy == nil]]) ifFalse:
			[^false]].
	^true!

markUnsatisfied
	"Record the fact that I am unsatisfied."

	self subclassResponsibility!

output
	"Answer my current output variable. Raise an error if I am not currently satisfied."

	self subclassResponsibility!

recalculate
	"Calculate the walkabout strength, the stay flag, and, if it is 'stay', the value for the current output of this constraint. Assume this constraint is satisfied."

	self subclassResponsibility!

satisfy: mark
	"Attempt to find a way to enforce this constraint. If successful, record the solution, perhaps modifying the current dataflow graph. Answer the constraint that this constraint overrides, if there is one, or nil, if there isn't."
	"Assume: I am not already satisfied"

	| overridden out |
	self chooseMethod: mark.
	(self isSatisfied)
		ifTrue:			"constraint can be satisfied"
			["mark inputs to allow cycle detection in addPropagate"
			 self inputsDo: [: in | in mark: mark].
			 out _ self output.
			 overridden _ out determinedBy.
			 (overridden == nil) ifFalse: [overridden markUnsatisfied].
			 out determinedBy: self.
			 (Planner addPropagate: self mark: mark) ifFalse:
				[self notify:
					('Cycle encountered adding:\   ',
					 self printString,
					 '\Constraint removed.') withCRs.
				 ^nil].
			 out mark: mark]
		ifFalse:			"constraint cannot be satisfied"
			[overridden _ nil.
			 (strength sameAs: (Strength required)) ifTrue:
				[self notify: 'Failed to satisfy a required constraint']].
	^overridden! !

!AbstractConstraint methodsFor: 'printing'!

longPrintOn: aStream

	| bindings |
	aStream nextPut: $(.
	self shortPrintOn: aStream.
	aStream space; nextPutAll: self strength printString.
	(self isSatisfied)
		ifTrue:
			[aStream cr; space; space; space.
			 self inputsDo:
				[: in | aStream nextPutAll: 'v', in asOop printString, ' '].
			aStream nextPutAll: '-> '.
			aStream nextPutAll: 'v', self output asOop printString]
		ifFalse:
			[aStream space; nextPutAll: 'UNSATISFIED'].
	aStream nextPut: $); cr.!

printOn: aStream

	(Sensor leftShiftDown)
		ifTrue: [self longPrintOn: aStream]
		ifFalse: [self shortPrintOn: aStream].!

shortPrintOn: aStream

	aStream nextPutAll: self class name, '(', self asOop printString, ')'.! !

AbstractConstraint variableSubclass: #Constraint
	instanceVariableNames: 'methods whichMethod '
	classVariableNames: ''
	poolDictionaries: ''
	category: 'DB-DeltaBlue'!
Constraint comment:
'I represent a system-maintainable relationship (or "constraint") between a set of variables. I contain a set of methods that can be executed to enforce the constraint. If I am satisfied in the current data flow graph, the method used to enforce the relationship is stored in whichMethod. If I am not satisfied, whichMethod is nil. My indexable fields contain the constrained variables.

Instance variables:
	methods			a collection of methods that can be used to
					enforce this constraint <Array of Method>
	whichMethod		the method currently used to enforce this constraint
					or nil if this constraint is not satisfied <Method>'!


!Constraint methodsFor: 'initialize-release'!

methods: methodList
	"Initialize myself with the given methods. I am initially not bound to variables."

	strength _ Strength required.
	methods _ methodList asArray.
	whichMethod _ nil.!

release

	strength _ nil.
	methods _ nil.
	whichMethod _ nil.!

var: variable strength: strengthSymbol
	"Install myself on the given variable with the given strength."

	self
		vars: (Array with: variable)
		strength: strengthSymbol!

var: variable1 var: variable2 strength: strengthSymbol
	"Install myself on the given variables with the given strength."

	self
		vars: (Array with: variable1 with: variable2)
		strength: strengthSymbol!

var: variable1 var: variable2 var: variable3 strength: strengthSymbol
	"Install myself on the given variables with the given strength."

	self
		vars: (Array with: variable1 with: variable2 with: variable3)
		strength: strengthSymbol!

var: variable1 var: variable2 var: variable3 var: variable4 strength: strengthSymbol
	"Install myself on the given variables with the given strength."

	self
		vars: (Array with: variable1 with: variable2 with: variable3 with: variable4)
		strength: strengthSymbol!

var: variable1 var: variable2 var: variable3 var: variable4 var: variable5 strength: strengthSymbol
	"Install myself on the given variables with the given strength."

	self
		vars:
			(Array with: variable1 with: variable2 with: variable3),
			(Array with: variable4 with: variable5)
		strength: strengthSymbol!

var: variable1 var: variable2 var: variable3 var: variable4 var: variable5 var: variable6 strength: strengthSymbol
	"Install myself on the given variables with the given strength."

	self
		vars:
			(Array with: variable1 with: variable2 with: variable3),
			(Array with: variable4 with: variable5 with: variable6)
		strength: strengthSymbol!

var: variable1 var: variable2 var: variable3 var: variable4 var: variable5 var: variable6 var: variable7 strength: strengthSymbol
	"Install myself on the given variables with the given strength."

	self
		vars:
			(Array with: variable1 with: variable2 with: variable3 with: variable4),
			(Array with: variable5 with: variable6 with: variable7)
		strength: strengthSymbol!

var: variable1 var: variable2 var: variable3 var: variable4 var: variable5 var: variable6 var: variable7 var: variable8 strength: strengthSymbol
	"Install myself on the given variables with the given strength."

	self
		vars:
			(Array with: variable1 with: variable2 with: variable3 with: variable4),
			(Array with: variable5 with: variable6 with: variable7 with: variable8)
		strength: strengthSymbol!

vars: vars strength: aSymbol
	"Install myself on the given collection of variables with the given strength."

	(vars size == self size) ifFalse:
		[self error: 'Wrong number of variables for this constraint.'].
	1 to: self size do:
		[: i | self at: i put: (vars at: i)].
	strength _ Strength of: aSymbol.
	self addConstraint.! !

!Constraint methodsFor: 'queries'!

isSatisfied
	"Answer true if this constraint is satisfied in the current solution."

	^whichMethod notNil! !

!Constraint methodsFor: 'add/remove'!

addToGraph
	"Add myself to the constraint graph."

	1 to: self size do:
		[: i | (self at: i) addConstraint: self].
	whichMethod _ nil.!

removeFromGraph
	"Remove myself from the constraint graph."

	| v |
	1 to: self size do:
		[: i |
		 v _ self at: i.
		 (v == nil) ifFalse: [v removeConstraint: self]].
	whichMethod _ nil.! !

!Constraint methodsFor: 'planning'!

chooseMethod: mark
	"Decide if I can be satisfied and record that decision. The output of the choosen method must not have the given mark and must have a walkabout strength less than that of this constraint."

	| bestOutStrength mOut |
	whichMethod _ nil.
	bestOutStrength _ strength.
	methods do:
		[: m |
		 mOut _ self at: m outIndex.
		 ((mOut mark ~= mark) &
		  (mOut walkStrength weaker: bestOutStrength)) ifTrue:
			[whichMethod _ m.
			 bestOutStrength _ mOut walkStrength]].!

constantOutput
	"Answer true if:
	    1. I am not an input constraint such as an EditConstraint, and
	    2. If I have any inputs, they are all marked stay."

	| outIndex i |
	(self isInput) ifTrue: [^false].
	self inputsDo:
		[: in | (in stay) ifFalse: [^false]].
	^true!

execute
	"Enforce this constraint. Assume that it is satisfied."

	whichMethod execute: self.!

inputsDo: aBlock
	"See comment in AbstractConstraint."

	| outIndex |
	outIndex _ whichMethod outIndex.
	1 to: self size do:
		[: i |
		 (i == outIndex) ifFalse:
			[aBlock value: (self at: i)]].!

markUnsatisfied
	"Record the fact that I am unsatisfied."

	whichMethod _ nil.!

output
	"Answer the output variable for the currently selected method. Raise an error if the receiver is not currently satisfied."

	^self at: whichMethod outIndex!

outputWalkStrength
	"Answer the walkabout strength to be assigned to the output of my selected method."

	| minStrength currentOut methodOut |
	minStrength _ strength.
	currentOut _ self at: whichMethod outIndex.
	1 to: methods size do:
		[: i |
		 methodOut _ self at: ((methods at: i) outIndex).
		 ((methodOut ~~ currentOut) and:
		   [methodOut walkStrength weaker: minStrength]) ifTrue:
			[minStrength _ methodOut walkStrength]].
	^minStrength!

recalculate
	"Calculate the walkabout strength, the stay flag, and, if it is 'stay', the value for the current output of this constraint. Assume this constraint is satisfied."

	| out |
	out _ self at: whichMethod outIndex.
	out walkStrength: self outputWalkStrength.
	out stay: self constantOutput.
	(out stay) ifTrue: [self execute].		"stay optimization"! !
"-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- "!

Constraint class
	instanceVariableNames: ''!


!Constraint class methodsFor: 'instance creation'!

names: variableNames methods: methodStrings
	"Create a new constraint from the given method strings. The expressions in methodStrings are compiled to produce the actual method bodies for the constraint. For example, the following builds a plus constraint:

	Constraint
		names: #(sum a b)
		methods: #('sum _ a + b'    'a _ sum - b'    'b _ sum - a')

The constraint thus created may be bound to actual variables with a specific strength (see Constraint>bind:strength:)."

	| methodList |
	methodList _ methodStrings collect:
		[: s | Method names: variableNames methodString: s].
	^(super new: variableNames size) methods: methodList! !