"
   Licensed under the Squeak License (the ''License''); you may not use this file except in compliance with the License.  You may obtain a copy of the License at  http://www.squeak.org/SqueakLicense/
"!
'From nsboot-2008-04-25.00 of 25 April 2008 [latest update: #0] on 28 April 2008 at 11:05:58 pm'!

!Behavior methodsFor: 'testing' stamp: 'sd 4/28/2008 23:05'!
shouldNotBeRedefined
	^false! !
	
!ClassBuilder methodsFor: 'private' stamp: 'ryan 6/13/2011 09:17'!
tooDangerousClasses
	"Return a list of class names which will not be modified in the public interface"
	^#(
		
	)
! !Object subclass: #Behavior	instanceVariableNames: 'superclass methodDict format mixinSlot enclosingObjectSlot'	classVariableNames: 'ObsoleteSubclasses'	poolDictionaries: ''	category: 'Kernel-Classes'!ClassDescription subclass: #Class	instanceVariableNames: 'subclasses name classPool sharedPools environment category metadata'	classVariableNames: ''	poolDictionaries: ''	category: 'Kernel-Classes'!!ClassBuilder methodsFor: 'private' stamp: 'ar 6/14/2010 22:06'!
tooDangerousClasses
	"Return a list of class names which will not be modified in the public interface"
	^#(
		"Object will break immediately"
		ProtoObject Object
		"Contexts and their superclasses"
		InstructionStream ContextPart BlockContext MethodContext BlockClosure
		"Superclasses of basic collections"
		Collection SequenceableCollection ArrayedCollection
		"Collections known to the VM"
		Array Bitmap String Symbol ByteArray CompiledMethod
		"Basic Numbers"
		Magnitude Number SmallInteger Float
		"Misc other"
		LookupKey Association Link Point Rectangle Behavior PositionableStream UndefinedObject
	)
! !!Behavior methodsFor: 'testing' stamp: 'ryan 6/13/2011 09:26'!
shouldNotBeRedefined
	"Return true if the receiver should not be redefined.
	The assumption is that compact classes,
	classes in Smalltalk specialObjects and 
	Behaviors should not be redefined"

	^(Smalltalk compactClassesArray includes: self)
		or:[(Smalltalk specialObjectsArray includes: self)
			or:[self isKindOf: self]]! !