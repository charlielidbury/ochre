Okay here is the transcript:

00:03 speaker 1: So in the beginning there was C,and that has loads of memory safety issues.And then we made C++ which improved it with like save pointers and stuff and has like enough types to do generics and things like that,so less type issues and stuff.
And then we made Rust,which is magical,and it fixed the memory safety issues,and that's through the borrow checker.And then we keep making more and more languages,and each one is more safe than the last.
Oh,and I guess I guess restrict this to like systems languages.I've been focusing on systems languages because obviously massive advancements have been this whole road is being done for non systems languages,butJust looking at system languagesAnd each time we make a new language,it's a massive pain in the ass.You have to like rewrite all your code and stuffSo the question is where's the where's the end of the road?Why is the end of the road there?If that's like no safety,that's like memory and type.Well,I guess there's assembly.
But memory and type safety,and then this is just like everything.
So the goal is that one.Like,think about what that one would do.
And then.
I claim dependent types would be useful for that because it's very useful in other contexts where you want to do theorem proving,such as theorem provers.
There are definitely theorem provers that aren't based off dependent types,but the majority are.
So yeah,the goal is to get a different type system into Rust.Well,I kind of,I have diverged significantly so from Rust that it's not really useful to say it in terms of Rust,but I've made another language which has a type system.
Which has dependent types and bars and stuff.
AndI think the most visible kind of way that this is,is like the thing that I'm unlocking here,is that if you have like,if you have a value,and then you have another value whose type depends on that value.
I think this is why you always get dependent types of languages and no mutation.It's because you mutate this,and then that mutates,and then this...I don't like...What does that mean?Like,did this just get initialized?Like,what does it mean to mutate when the types depend on terms?So...
This,I thought,was a pretty good explanation as to why modern languages with mutations don't have it.
And then...
And then you have,there's a couple of projects.
These are successful projects which convert Rust to pure function code.
So safe Rust,which is quite a large caveat,to pure function.
And then I was kind of like,well,something here.
If this safe Rust conveys the same information,the same underlying concepts as pure function code,then this issue should be solved somehow.
And the particular way that I've done that is...Aeneas.
Aeneas is the Greek god.Have you said that?I always get it wrong.Aeneas.I'll give you an Aeneas,man.

03:36 speaker 2: This gets over Aeneas or Aeneas.

03:38 speaker 1: Aeneas sounds wrong.
So,Aeneas defines an abstract interpretation.

03:45 speaker 2: Yes,he does.

03:48 speaker 1: There's an abstract interpretation which...
Russ has a little thing called the MIR,which is the middle something interpretation or something,and this works on the MIR.
What it does is it converts the MIR to pure functional code.
Specifically me,working on the Cockback end.
This is useful.So I originally sat down to do this,but then on...
So I think what I'm telling you right now is kind of how I got to the solution,but in the actual report I'm kind of supposed to just go to the solution.
Okay,is this good background?

04:25 speaker 2: Yeah,I think it's good background,but alsoI think it's a,generally speaking,a mistake to go straight to the solution.
Because if you think about when you break papers and they've presented you a solution,

04:38 speaker 1: You're like,

04:39 speaker 2: Wow,they magic'd this up.Occasionally...
You're like,wow,this is really easy.I've had papers,I've seen papers rejected because the paper is so well written that the reviewers are like,you know,there's nothing like technical here.
Because,yeah,I found it,and they're like,what they're missing is the years.
Of work you're thinking it to that point and they've sort of removed that story the thesis so this is convincing them all that it's power working yes okay so that's what that's the thing is that you're i mean for markers like nick and stephan they probably understand that butyeah it's good to to demonstrate that storybecause you're showing how you've encountered challenges and overcome them and it becomes much easier to evidence,if you look at the map scheme,that you have overcome technical challenges,as opposed to,yeah,I did it.

05:34 speaker 1: It worked,yeah.
There's the diving rules.Go nuts.Yeah,

05:38 speaker 2: And that's got a sort of aura of like...
Okay,sounds like that was easy then.

05:45 speaker 1: Yeah.

05:46 speaker 2: Which is what you're trying to avoid.

05:49 speaker 1: Where was I going with this?Yeah,this is typed.
And I know it's typed.
And so,Aeneas takes in typed input and returns this typed Lean output.And then the idea is that now using Lean,well actually no,they use F-style.I think they also have a Lean back in there,or a source back.
The original papers have stopped.
Then you can use f-style to reason about f-style and the reason why that works is because you don't care about the performance of f-style so any mutation you can just make into like an ugly substitution or whatever thing so the aim here then is to take the rust program andbasically reason about it on the side yes and then you go back to just using the rust program yes yeah you compile but you compile and run this but then your proofs are about thatAnd then this translation has,I don't know that they've actually done proper correctness preserving property,but they've done a lot of argument in the paper saying that this is definitely correct.
Anyway,my plan was to takeRust and go to like,dependently typed land or more or whatever and go to pure functional land and then bring the type annotations over as well.
But it turned out that the abstract interpretation that they're doing on this.
I'll just write it what the hell you abstract environment Omega andThen you have a term syntax the language or was it like I do in the country term syntax the language abstracts and turretsAnd then over here you have the type that it interprets to so the abstract interpretation tells you what the type is for a given term andSo that what they were doing is that other solid effect of this abstracts interpretation It was producing this pure functional languageBut actually it turns out you don't need this step at all,because this abstract interpretation can just do the type checking.They were relying on the MIR to do the type checking,so I've now added type checking to the abstract interpretation they defined.
So all of my judgments look like this,where you end up with a new environment on the end.

08:09 speaker 2: So the question I have is...
Abstract interpretation is not necessarily leaked,

08:15 speaker 1: Right?

08:17 speaker 2: There can be things that are from the outside world that you can't see.I don't know if this is a general problem with dependent types,is that you can't depend on inputs.

08:27 speaker 1: I think we're going to work on it.

08:29 speaker 2: It has to be statically known.
But what happens if the abstract interpreter does not reach?a reduced term is it just a more abstract type that comes out and you could say nothing about it yeah so this yes basically I mean this I've already hit you too many details but this T has got a syntax which

08:50 speaker 1: Is something something something somethingSo if you union together things that can't get unioned,you just get top.So there's always an answer here,but it just might be top and that means you have no typing in place.
There's also this concept of type widening.So any environment,this operator here,It's called a rearrangement.This is anAeneas thing,this operator,but I've extended it.
This is a rearrangement,and at any point you can do this to context.There's more of a housekeeping thing,and one thing you can always do is widen a type.So I've got subtyping.
So one of the types is...
Now I'm thinking maybe I should have said this in different order,but one of the types is a set of answers.
Where like this value here,one of the pieces of syntax you can write.
God bless you.
Savage sneeze.

09:49 speaker 2: It hurt.You know like when a sneeze decides to backtrack down your throat?

09:54 speaker 1: Oh,like the pressure.
Yeah,one of the things you can do is you can construct these things for lessons.So I think this one of the paper,it's like the primitive type.
It's runtime representations of the string you've got off for the record,not that it really matters for the theory.Like you have like,that's also 32 bits as well as.
Oh,the type of this is that.
And it's also every supersense.
So some when you go back to somethingAnd then it's always valid to forget to like the information with these rare in birdsSo you could always if you've got something of a type a you can always hit some type a B.YeahSoI guess I'll switch gears a little bit to like howKind of like a motivating example like somethingLike like that in rustconfusingly that is a thing that has runtime length.Yes.Whereas in theory land,it's got people refer to it as compile time.
Should I just,for the sake of Nick and Stefan,I'll probably refer to it as compile time,no length.And just say like list equals something.

11:13 speaker 2: Statically no length.

11:14 speaker 1: Yes,statically no length.
Yeah.
So in Rust,if you define what is like the equivalent of list.what you want is like a pair where you have like the length of the list and then the list itself um we are only going to support lists ofAll right,that's kind of what we want to express.But in Rust,this is a raw pointer.
Yeah,you have a,I can't remember what it is,but it's a bit of this funny syntax,raw pointer,basically,saying we don't know what the type that we're pointing at is.
And this is bad.It'd be nice if we could do,actually type that.And this is an example of a dependent.
This is a sum type.
So in OCA,I have some types.
I won't be simplified for now,but I've got dependent functions,which areT, U,and then independent pairs,which are T,U.
Where those are capitals because they're actually syntax like this here is actually just syntax you can use to calculate the return value.
So it's not like an input type and output type,it's syntax that generates types.And you use this other abstract interpretation like that to generate that.
But yeah,that in mind,this is an example of that.
Where you have left and right and then tricky cases like if I have a function where I've got a listof naturals and once they knowSo if I have a reference to a list of naturals,stuff starts getting interesting.So this is all just understood stuff that we get from the function line.So this literally returns just unit.
This is my function syntax.
So this should be that I should be able to go.
0 is2 and 1.Is42 this is how I choose to represent.
So,no,I'm in definition.
It was a definition of that,

13:57 speaker 3: Which is.

13:59 speaker 1: 0 is.

14:03 speaker 3: Yes.

14:07 speaker 2: Okay.

14:10 speaker 3: So.Yep.

14:13 speaker 1: So,pair.
And then,probably not by the time I submit,but in the future,pairs won't be boxed.
So this is just what an array is.This is a continuous in memory array.
So this should be valid.But it's really hard to type check.Because,like,So I have to express it like this.I don't want to express it by returning a new list or doing L equals.Because I'm trying to do these in-place mutations into a structure.
And then this can be efficiently changed to a Sunday code.So the great and the awkward bit is here.What's the type of L?It's kind of invalid,but also you do know some things about it.
Because you don't know what the length of it is before,so I could have put the wrong value in here.
Like a valid instance of L here could be.

15:07 speaker 2: But it doesn't matter,right?Because the Ls are existentially typed in that you know they do have length and the things that are inside them match together.
But you don't actually care about what comes next.You're saying I can change the length if I want to.
That's not exposed to the type.There's no contract for that.But there is an oddity,yes,between those lines where...
The type can actually mismatch.

15:37 speaker 1: Yeah,so the type temporarily mismatches here.
And then through very complicated mechanisms,the abstract interpretation of this is just fine.
Because,soWhy don't you just write something up and walk away?

15:54 speaker 2: So this is interesting because my first thought about this is something to do with having a block in the language that says invariances can be broken within this bit as long as they're restored at the end.
I mean is that totally what's happening?Yes.Yeah.

16:16 speaker 1: Yes.Um,the the block is the function Yeah,so if you have there's this funnyFunny thing in there where you can be likeX is food and then you can be like X is barBut these are different types.Yeah,we're doing a strong updateNow I can also sayX is food bar and all of this is well typedIt doesn't associate the type with the identifier X.It'sX and a point in the program.Right.

16:49 speaker 2: So the rule would just be that on exiting the function,X best go back to the type it was originally.Yes.

16:55 speaker 1: The specific way that is,is.
Functions must destroy everything they created,so they must drop this from memory and any local variables they made,they must drop from memory.And the behavior of dropping a reference to something is putting a value back.
So if I have,this is just,let me ask,but I have this code here.
This is RAST.
I have something called the abstract and blur.
And the abstract environment maps,well this is a good time to introduce the abstract environment.
That says x is 5 and then I say...
So that's a new exclusive reference to x.If I did a,just a,outbound matter it would do something different.
And now there's no 5 here.It says this has been loaned up mutably to loan L andThen Rx is the thing that has mutably borrowed data.Mm-hmm,and then that's got the 5 in itRight and then if I pass this to a function first off,this is how it detects like ifI doOkay,actually if I do x here and use x,this is valid because what it'll do,and this is a brain arrangement,is it will end Rx,put the value back.
So it waits for the last second and then it ends whenever you request it.
And then this would be invalid.
Yeah,because it's ended Rx,but then this would be valid again.
And yet the specific way it does that is it has these inserts drops.
So it says drop Rx,and then the behavior of dropping a musical reference is to restore the value back.And then that then tied back to the promise that functions make where they will clean up all the memory of them because cleaning up this reference.We'll put the bunny back.
And then if you put something back into the original hole,which isn't the type nav,list nav,it looks like.

19:16 speaker 2: So what happens?

19:18 speaker 1: If,

19:18 speaker 2: In between the two lines,at the point where we do have inconsistent state,what if I passed L to a function?

19:28 speaker 1: What error would I get back?You actually,you don't necessarily need to get an error there actually.

19:34 speaker 2: Well,let's say the function took in N.Yes.

19:39 speaker 1: I will answer this question by writing down the L-shaped environment at each of these lines.So,

19:43 speaker 3: Let's say I have a function that is in the L-shaped environment.

19:58 speaker 1: To any list of n.
So maybe first funny thing is that I don't,every value is its own type.
So in the same way that saying or l five is valid,so in the or l a whole thing is valid,of course.Yeah.

20:20 speaker 2: Unfamiliar with this.

20:21 speaker 1: Subtyping.

20:24 speaker 2: Scala 3,every value has its own type.

20:26 speaker 1: Oh,that's really cool.

20:27 speaker 2: That's why you can do type number arithmetic on them.Oh,not for now.You can save fun stuff like Xness type 8,X equals 3 plus 5.

20:37 speaker 1: Yes,you can do that in Docker as well.
And TypeScript.
What was I saying?Yeah.
Parting value.And then I go L...

20:48 speaker 3: Ah.

20:50 speaker 1: So this is not actually what's stored in the context,it's what is evaluated.
So this is going to be a pair where the left is a nut and the right is...Again,this is...Yeah,it's stored as syntax actually.
So that's what stored in the thing.And then I'm going to go l dot.So at the moment,let's say I access the write.What's the type of that?What it will do is it will get what it knows of your l dot zero,the write inside,which is nothing.And it will write that to the syntax here.
And that will change the context it'll put in the context so now we have L is a mat andThen it will get this and evaluate thisThis squiggly means value is at the type level and get that and evaluate and what it'll get is starbecause it's going to try and union unit with a pair so this is just this is just the ok aware of saying there's nothing you know about this value yeah and then so i have i have question suppose i had already at some point in this function said something like l.0 um greater

22:26 speaker 2: Than two yeah does that context reflect that actually the reduced type is going to be a a star

22:37 speaker 1: Yes,it does.So more specifically,maybe,I've got case statements.And the only thing you can split a case on is an atom.
So I goL dot 0,which is the NAT,and then I go dot 0.
I will show you what the representation of NATs are.

22:54 speaker 2: Are they PNROs?

22:55 speaker 1: Yes.
But it's a dependent pair.Like ADTs and OCA are just dependent pairs,where the left is the tag and the right is the payload.
SoNATs...is the tag is it is either zero or successor and then the right depends on leftand if it is zero units it isYeah,this is rubbish.

23:47 speaker 2: So you're encoding constructors there,basically.

23:50 speaker 1: Yeah,although they are actually no different from functions.They're just functions that return types.
Yeah,that's rubbish.
Yeah,there is some tech things that I've all learned.
By the way,there's a lovely sentence.
This can actually,this will get expanded to the above.This ball operator can be used.
So that's how you average program would write that definition.But that's what's actually stored in the abstracts.That's the actual thing.This is not a type thing.This is a constructor of types.
SoI am going L dot 0,which is a NAT.
Which is a NAT,and then I'm going.0,which is that tag.
And so now I can say,if it's 0,then do something.
And if it's slack,then do something else.
And in here,L.1,what was the type?That will be unit.
So I'm just going to start with that unit.
And then you could just do brackets equals.
And then that one would be nat star.
Yeah,because it's a.
Yeah.
And then you can actually case again on L dot 0 dot 0 dot 0Because in here,you know that you're in the sub case and you know that this so nowl dot zero zero that's our tag for our first natural so and that's the right inside and then that's the other tag there will be syntactic sugar you do want at some point yes but this will then match on the predecessor yes on that this is prayer yessyntactic sugars i think there's a way to generically get match statements and compile under k statements where because the onlyIt should only boil down to pattern match with atoms because everything is either an atom repair or function or a reference.
Where was I going with this?Yeah,that's how pattern matching works.So that's type narrowing.

26:20 speaker 2: Yes.

26:20 speaker 1: You read that.The way this is implemented is every time you do L.1,it actually uses this syntax to evaluate L.1.
So there is not so much a value stored for the right-hand side.It's the syntax which generates the right-hand side.
What was I saying?Oh,yeah,I was going to write out the...Yeah,so what does the abstract environment look like if you're midwinter?Yeah.Do you have any questions,Cruz?No.
What does the...
So if I do L.0,what does that make this look like?There's a bar.
And then I didn't actually set it to anything.
Well now this left hand side is just a 2,and the rule that gets from here to here is very complicated,but this just goes,it just goes,okay,well,what is the right hand side,given what I currently know about the left hand side,because I'm about to figure it out.
And then it will put this in there,evaluate that,and get started.
Yeah,so at this point the right hand side has been completely forgotten.
I think for practical reasons at this point I would actually need to run drop number one.
Because otherwise I don't know how to drop this finally because I don't know what type it is.So when I forget about a type I should probably drop it.
So this is what the thing is now.And thenI do L.1,and then if you put an implicit unit there,and this...
So that's put it in there.So we've forgotten the dependent because there isn't a dependence because it's just it's a specific value.
And then when the function ends,it runs drop L.
And part of dropping L will ask the question,is that a subtype of?list that.
And then it's just the typo for our surface,

29:02 speaker 2: So type the same thing.

29:03 speaker 1: And then expand that.
42,

29:13 speaker 3: 42.

29:22 speaker 1: It will do that substitution there.
And that gets something that looks like that,and then this will project.

29:39 speaker 3: Yeah.

29:45 speaker 1: Yeah.Any questions?No?That's dependent pairs,pretty much.
And then dependent functions are very similar.It uses the same syntax,where it stores the syntax instead of the natural binding.
I don't know.

30:00 speaker 2: I don't know.

30:02 speaker 1: I don't know.I I don't know.I I I I don't know.I don't know.

30:04 speaker 2: I I I I I I I I I don't

30:12 speaker 1: If I have a function,let's just start with,let's start with the non-dependent functions.
I take it in that,and I return that,and the implementation is identity.

30:28 speaker 3: Yep.

30:30 speaker 1: And then I'm going to do it five.

30:38 speaker 2: Isn't the more specific type of that n of type nat to n?Yes.

30:45 speaker 1: That was going to be my segway when I got onto the dependent functions.
I'm going to get there anyway.
Bolt-hit is in here and then we do id of...
Id of 5 and then the type checker will go this is of typeNAT because what it's done is it's got this type written it into this syntax here and then it's got that syntax right i hope and it's gone back and then do you getThere is an environment pulse between those two.
Yeah.
Yes.Then if this is not that,this is N,then it said you can't tell that it.Change that to N and now we'll observe in this case.
Yeah.
Yeah,so one way to look at functions is just these are both function bodies really.
It's just this one is forgotten and this one is run every time it calls by.
So if there's something expensive you want to do,you do it in here,and if there's something type-bubble you want to do,you do it in here.But they can both contain the same thing.
So like...
Oh,one thing,this is more of a taste thing,butI think in the actual thing and maybe in the typing rules as well,I'm going to kind of currently be doing everything with a capital letter is erased.
So capital V VEK is erased at compile time and then anything lowercase that kind of mirrors what you do in Haskell types of roughcase.
So you have two two versions of functions,one of this and then a version of a function which can't exist at runtime,which is just a bodyless function.
Like this and it has to be assigned to a compile time only very that's how that has to find so that could be that again I'm gonna do better than that soa match no taking normal oh I mean I'm gonna doSo I could write here,is a type start.

33:04 speaker 2: So your capital letter things are what a Haskell program would roughly refer to as a type family.

33:15 speaker 1: This is also a capital letter thing.Yeah.

33:17 speaker 2: Which I think is...

33:18 speaker 1: Yeah,I guess.Yeah,I guess because it doesn't...

33:20 speaker 2: It's just a type alias.Yes.

33:23 speaker 1: Well,it's all type aliases,really.Yes.
Yeah,it's like if a type family could return lots of types as well.You could also return a value because your values are types because you have the scalar system.
But every type,every value is the same type.

33:34 speaker 2: So you could have an erased function.Oh,okay.
So your erased functions are basically just inline functions saying,I can do lots of computation but in the end my body won't exist.
Or rather something,yeah,the function doesn't actually have to happen.

33:52 speaker 1: So in the abstract world,no,the function definitely doesn't,it shouldn't.Yes.Because we're type checking,we're not evaluating.Yes,

33:58 speaker 2: But there is,so again,that's two extremes.
You have the function that needs to be type checked that does something,the function that does nothing but needs to be type checked.There's also,yes,a middle ground somewhere in the middle,which is.
Function that is guaranteed to run at compile time but produces something.

34:22 speaker 1: Well,this produces a compile time value.

34:30 speaker 2: Yes,it does.I mean,guaranteed to run at compile time but reduces a runtime value.

34:37 speaker 1: There is really no difference because if something is,if you can reason about a runtime value,you can reason about it at compile time.

34:44 speaker 2: Yes,that's true.

34:45 speaker 1: So this,this,despite being a five,is a compile time value.
Yes.

34:53 speaker 2: Yes,it's difficult.I guess the thing that I'mForgetting,of course,is that all values are both runtime and compile time.Because what I'm thinking is effectively the staging argument where you can say,I know about compile time things.
I can therefore eliminate a whole bunch of computation by doing it now.
But I still result in ephemeral dynamic computations that I did as a byproduct.So I can't reach that.So you've separated between...
I erase the bits I can reason about and I leave the bits I can't.

35:30 speaker 1: Yes,yeah,so everything I just,yeah,everything I can't reason about,I chuck in a runtime.

35:37 speaker 2: Yes.
But the outcome of that is you can guarantee that the function call itself doesn't happen.It's just,once it's type checked,it produces the body and just says,here you go.

35:47 speaker 1: Yeah,yeah.

35:51 speaker 2: If you don't do that,I suppose what you're generating is you're generating a specialized function that says I haveDischarged all of my static information and I am me

36:02 speaker 1: Mmm, so in an OCHR I think what that would look like would be a functionWhich takes in which takes in a compile-to-erase thing.This is no longer thereAnd then takes in a runtime value,so lowercase runtime value.

36:18 speaker 2: Yes

36:20 speaker 1: Something this.I think this would just be how you'd express monomorphization.Yes.Because you have this problem-time argument which generates this problem-time.Yes.

36:28 speaker 2: You're doing specialization there,where you're saying I can specialize on a type A.
And I will get back a representation of some known length later.

36:41 speaker 1: Some unknown length,rather.

36:44 speaker 2: Unknown in the sense that it's not known currently.
Yeah,interesting.
It's like a very weird mix of metaprogramming in a garter of three features.

36:59 speaker 1: We have this arrow,which is abstract interpretation,but this is reading about runtime values.And I have this one which is compile time values.
And then gradually over time all the typing judgments of these kind of kept,I kept finding ways to make them more and more similar to each other.
And I was like,these are really similar.
Up to and including like some things you always you can just consider there to be like an infinite universe spaceWhere like instead of saying this you could just say this is the ground one and then I have yeah the level aboveThis is called

37:35 speaker 2: Some person's name interpreters

37:41 speaker 1: I can't remember what the name is.

37:42 speaker 2: It's the multi-stage programming.
Multi-stage programming is related to this,what you have.Things up at level 0,

37:50 speaker 1: 1,

37:51 speaker 2: Up to N.
It's probably useful for you.
Oh,it's so close.I think it's a Japanese name.

38:04 speaker 1: If you could pop that in myDiscord DMs,I'd remember it.

38:16 speaker 2: This is so not going to work with that Googling.It just was like interpreter,Japan,and I'm like,no,that's not going to give me what I wanted.

38:26 speaker 1: Abstracts and Terpsation with an Infinite Series of Universes.

38:39 speaker 2: Projection.

38:41 speaker 1: Because.

38:47 speaker 2: Something projectionI'm so close yeah for tomorrow for tomorrowum yeah it's related to partial evaluation and it's uh basically that you have um in different sense level zero is interpreter level one is compiler level two is compiler compiler yes yeah and so on umyeah so yeah future projections yeah yeah there we go might be useful um

39:30 speaker 1: I'm not sure I should have done that.

39:37 speaker 2: There we go.Done.
Three senses of my mind unlocked.

39:43 speaker 1: They had chosen not to do this in 3D.

39:45 speaker 2: I noticed it and I was like,

39:46 speaker 1: This actually seems like it would generalize quite well.Because you have some rules,you have some rules,with typing judgments like this,where you have like,that's defined in terms of sacraments.And then you need the level above.Yes.YeahLike um,

40:01 speaker 2: Yes,although I think in practice

40:03 speaker 1: This happens when like applying function.

40:05 speaker 2: I think in practice you really have to get above oneAnd sometimes you get to twoYeah, it's likeYeah, it's kind of an odd scenario when you'reyou're trying to leverage static information about your static information.

40:26 speaker 1: I thought this could be quite cute in the future if I ever do method programming.Yes.
So,tangent,obis-code.
We have two arrows,and one of them is squiggling.Yes.
So,this is squiggled,and that body is fat-arrowed.
And this body is only of a fat-arrow at once.
Check that it's correct and then the squiggles happen every time you try and figure out types.
Oh yeah,back.
Take them on A and it takes them to NATS and then it returns a...
What NATS is.
Thanks so much.
So this,it's just a return type.
So there's not really any syntactic separation between the two.
It's just by being in that location in the syntax,you know how that is at convoluted.Yeah,

41:49 speaker 2: It feels like match type.

41:59 speaker 1: That,I think,is kind of the important bit.
Any questions,Chris?There's a horrendous amount of typing rules.

42:11 speaker 2: I'm sure there are.

42:12 speaker 1: It's awful.I have a table.Because what you've seen of these two,you also get writes,like that.Because you can write to syntax.
So now we've got four arrows.
And then this is a move.
And this is a rightThese are destructive operationsWe're like this right must be landing on an initialized valueAnd the way you do that is by dropping the boat and this move will leave an initialized value behindIt'sBut you don't always want that like a case doesn't need to destroy the thing that is matching so then you also have reads andType narrowingThen there's six arrows.Then I have my AST is like eight strong,whatever.And then I have a big table of each arrow versus an N,and aT, and a thing.And then each one of those squares is a typing rule.

43:25 speaker 2: I think it could be less.

43:27 speaker 1: I really want to get less arrows.I feel like six is too many.I started off with two,a read and a write,and then it just gradually escalates.
I think I'm actually going to put in my future work section,syndrome.
Because there's so many similarities between the definitions of these,like the things.Like,oftentimes move and write are justlike they're very similar like it move the right first if you get variable X and move it and you get a variableV then the way you get that is you get the new environment is just the old environment but you have X points toThis is right.
There are no similarities between all sex.
I've given up trying to simplify them,I might just have loads of repetition in my final report.
Because these rules are quite simple.I mean,

44:49 speaker 2: Are they always just upside down?

44:51 speaker 1: No.Definitely not.
There are subtle differences between all sex in loads of places.
Then for like every constant I just have six poppies?Well,I do this with a for all.I say for all arrows.But it's like tick A goes to tick A.

45:11 speaker 2: I reckon it's...I put my Nick Wu hat on.
I'm sure he would say something like,

45:18 speaker 1: Oh,

45:18 speaker 2: They're just...
They're just kind of arrows to each other and they're all in different categories.

45:28 speaker 1: I think there are very obvious properties of these things.If you get any syntax m,you move a value v from it,and then you put that into the syntax m,you end up where you started.
This is a lemma which I don't have a proof for,but I'm sure you could.

45:50 speaker 2: I think it would be good to give laws the interactions between these arrows.

45:57 speaker 1: I mean,what happens if you...

46:01 speaker 2: A move and write always canceling on the same thing.If you move something and immediately write it,is that an identity?

46:10 speaker 1: Actually,it's not quite,because in order to move something,you might need to do housekeeping.

46:17 speaker 2: So those are the interesting ones.

46:19 speaker 1: Because to move something,no,no,it is always here.

46:26 speaker 2: These are good things to point out.

46:28 speaker 1: There's this big property which I want to prove,which is if you start with the entity can't...why is this...this pen has been great for like the whole time I've been at home.
It is.

46:38 speaker 2: Is it this room?

46:39 speaker 1: It is the curse of this room.

46:40 speaker 2: It's been killing pens like...

46:41 speaker 1: What was me earlier?I've used this pen for months,constantly on my whiteboard at home.
If you get any piece of syntax and you do abstracts interpretation on it and it says one other thing of V.And then you also get the same piece of syntax and you do concrete evaluations.This is just an interpreter.It helps if it's actually really simple.
Or is that a k?Then k is a type e.That is my big.
I do not have proof of this,but if I did,that would be lovely.
Improving this,I will need all sorts of learners.I think,like all these nice properties about arrows.

47:20 speaker 2: I definitely think it would be interesting to try and improve properties about the arrows'interactions with each other.
Yeah,because it might be that you do just have six.
There's nothing wrong with having a headache.Yeah,exactly.But...

47:39 speaker 1: Because if you,like,there's a big table,a majestic table.

47:52 speaker 2: The interactions,or the possible outcomes of various error combinations in Parsley.I put them into a table and there was one hole in it.I was like,huh,

48:02 speaker 1: There's a hole.

48:04 speaker 2: Everything else is covered,but this one hole and a generalized combinator filled the hole.It was very pleasing.

48:11 speaker 1: Yeah.
This is my table.
Yeah.Read,write,destructive,non-destructive,compile,don't write.The reason I used to have eight is because it used to be like a three-dimensional table with destructive,non-destructive,read time,write time,comp time,run time.
And then what I did is I said that compile time doesn't have moves.But all of the concepts of moves make sense at compile time.But the only reason to do move semantics is for manual memory.And at compile time I just reference count everything.
I do not need move semantics.

48:43 speaker 2: I don't think that this is any more complex than it needs to be.

48:48 speaker 1: That's refreshing to hear.Stefan almost had a heart attack.

48:51 speaker 2: What,with six?

48:53 speaker 1: Well,I don't even think he's really sore or so.

48:56 speaker 2: Yeah,I don't,I think that they're very clearly distinct.

49:02 speaker 1: One thing that I was thinking of doing is making it like one arrow,but with different modalities.Yeah.And then...

49:08 speaker 2: That doesn't really save you anything,

49:09 speaker 1: It just...It doesn't save you complexity,it just makes it syntactically easier to state them all.

49:14 speaker 2: Yeah,it does save you typesetting.There's a parts table.

49:22 speaker 1: I'm attempting to write it out.I've got the old version.

49:26 speaker 2: I think I've seen a lot worse.

49:29 speaker 1: Here's the...this is like all set.

49:33 speaker 2: I have seen typing rules that make me know the string.

49:38 speaker 1: And these are the two that's just how you get them right in there because you have to figure out the right description

49:49 speaker 2: I appreciate that you actually have more amounts to comments.

49:54 speaker 1: I know,gold modern typing people don't like comments do they?And also they just like this.

50:04 speaker 2: Jesus,you are a menace.

50:05 speaker 1: This is the spawn of the devil.Whose fucking idea was a 2D thing?Yeah,we figured this out.It's called code.You go A and then B and then C.
And then I wanted this.I just go A and then B and then B.1,B.2,C,C.1.
It's beautiful.Easy.We figured this out already with code.But no.
We do this and then I can't write it.

50:32 speaker 2: My favourite thing is the fact that they grow upwards,they should grow downwards.

50:36 speaker 1: That's yes.
Stefan literally teaches type systems the first lecture.He's just doing all this upside down.

50:41 speaker 2: Do you know that the fundamental difference between mathematicians and computing people is the direction they grow their trees?

50:50 speaker 1: And mathematicians go upwards.

50:52 speaker 2: Mathematicians go upwards,computing people go downwards.

50:55 speaker 1: Well,aren't we smart?Because this is better than that.I don't actually prefer this to doing it,because look,that.
This is just great.But also,and it reads like code as well.

51:06 speaker 2: The problem with going up is that you run out of space.Yeah,you have to guess ahead of time.Yeah.

51:14 speaker 1: You have to do the same with this even if it's upside down because it's 2D.

51:17 speaker 2: I mean,yeah,because you can grow horizontally.

51:20 speaker 1: Yeah,which causes significant problems with type system students.
You just end up going...
Okay.
Your lack of pointing out major problems is...
It's great.

51:43 speaker 2: I mean,yeah,it seems straightforward to understand.

51:49 speaker 1: Nice.
Well,I'll write that up then.

51:53 speaker 2: Yes,I'm wondering.I think the only thingI was wondering about,

51:56 speaker 1: Philip,

51:57 speaker 2: Was loops.
Do you have loops?

52:02 speaker 1: No,but I think it's possible.

52:05 speaker 2: Yeah,because loops are interesting because I think the idea would be you would actually want the invariances to hold after the end of the loop body.

52:14 speaker 1: Oh,like in my pre-planned kind of thing?

52:17 speaker 2: Well,in a sense that I don't think what you would want,

52:21 speaker 1: I think

52:21 speaker 2: I can demonstrate that this is the case,I don't think you would want to have an inconsistency between the end of a loop and the start of the next iteration.

52:29 speaker 1: I think the way...
See,

52:31 speaker 2: The way you do that by saying it's a tele-requested function and to call a function you must have consistency because you've got the drop.

52:38 speaker 1: Yes,or you put as a primitive,you say that the body of loops capture everything usefully.Yeah,both of that.Yeah.So.
And like,if you,the way that that called drop thing is involved,it is fine.
Hmm.
It will have a function int n.
And I want to apply a value V to it,thenI get my context,and then I putV in M.
And then if M is like a pattern match,or if it's just a mix or something,that'll put something in there.
And then I pull the return value out of M.
What am I doing here?W.
And then...
I put the original context back and then for this to hold it must have done all the cleaning up of video which also has the nice property making it quite implementable becauseI just have one context which I always play around it doesn't really fork yes

53:45 speaker 2: So,I think the one missing bit you've got is...
I mean,clearly you haven't made it to infinity,right?In your very original line of abstraction.

53:59 speaker 1: So you've got,

54:00 speaker 2: Like,assembly C rust,and then you have infinity at the end.

54:03 speaker 1: I don't know.

54:06 speaker 2: So...

54:06 speaker 1: Well,I don't know.Four dependent types.
Well,I'll just throw a theorem through.I don't think this is a sound logic.
But it could be the right direction.

54:17 speaker 2: I'm sure it is the right direction,but I think it would be good to say,you know,where are you and what can't you do?Because I'm sure there is a limitation.

54:31 speaker 1: I don't...I haven't really found exactly what you can and can't do.
I suspect if anything it'll be that you can do everything but it's just permissive such that it's unsound.
Yeah.
But I don't think there is much of like a...I have no idea what the formal correctness of this is,but it feels like it depends on the true and completeness of theorem.Theorem Provers only differ in power.
Things like,you are a Theorem Prover all of a sudden.I'm probably not going to be able to claim this is a Theorem Prover,because it won't be,like,I won't have sorted out the logical foundations.Yes.

55:10 speaker 2: So the other thing that I think would be really,really cool is early on in your introduction,you have an example of a broken program.
You don't tell me that it's broken.

55:26 speaker 1: Oh,no,a time-jacket and show that it's broken.

55:28 speaker 2: It's your conclusion down the street,actually.
This innocuous-looking program was broken.

55:34 speaker 1: That's a good idea.

55:37 speaker 2: It's the sort of narrative trickI love,because it catches people off guard.Yeah.I always appreciate this.

55:44 speaker 1: That's a good idea.I'll have to think about what kind of program.Hmm.
Hmm.

55:52 speaker 2: Yeah,bonus points if you can make the initial example a compelling reason why you'd want dependent types,and then later on demonstrate there was a bug that you probably missed.

56:01 speaker 1: Because there's a balance of it.

56:04 speaker 2: Yeah.Yeah,I like that sort of thing.

56:07 speaker 1: That's kind of the example that I always go back to.
Is that VEC case because in Rust it's done on safe code?Mm-hmm.So I can say in the standard library is unsafe because we can't capture this type in relation.Yes

56:24 speaker 2: Yeah, that's trueBut you know,I mean this all roughly makes sense.
The challenge is that it's often quite easy to explain these things on a whiteboard.
It's a lot harder to explain it in text.

56:42 speaker 1: Yes.
I'm going to get this conversation and then like,I'm going to just get the whole thing put in chat gpt 4.0 and then get it to like make me a like a written version of it and then just ask me like what are all the questions that Jamie asked and like what's the rough outline of what I said and like where did I where did the narrative not flow nicely

57:11 speaker 2: Yeah.
I'm not sure how many of my questions are actually pertinent.

57:18 speaker 1: But again,a lot of questions,and that shows that that basic explanation kind of works.

57:24 speaker 2: Yes.Some of the questions that I had,I guess,yeah,they were thoughts that came out of something that you said,but not necessarily a misunderstanding.It's like,okay,I see how this works.Can you do this?

57:37 speaker 1: But then it might be a nice part of the report.

57:42 speaker 2: I liked the fact that,I guess the thing I was pointing out earlier is,do you have a sense of flow typing?Flow typing was what I said when I said,if you could say L.0 is greater than 2,you know underneath that scope.

57:59 speaker 1: Yes,yeah,yeah,funny enough.

58:01 speaker 2: So flow typing is one of these really interesting things.You get the point sometimes.I think the thing I'm most exposed to is Scala 3's got flow typing for nulls.So if you're on the explicit nulls language flag,if you do a null check at some point,it will refine the type of the thing you checked against so that it does not include null for the body that's covered in that check.

58:26 speaker 1: That would happen here if you defined like greater than in the this bit here.
Yeah.
If you defined it in a compulsory way.

58:39 speaker 2: But you could in theory also do it.the runtime way where you kind of want to check at runtime so if i have case x greater than two or something in the greater than two if it's not whereas there's less than two i

58:57 speaker 1: Believe in there x will have type it will be only permissible to have like zero units or suckzero unit.Like I think it would actually do the narrowing.
But it would just do it in a really inefficient way with all these different places.And then this would be loads of match statements.And then I think you'd get the same in the true case where it would be likeSo this is a gross that take.So it would beOne strenuous just die.
I think that would be the type of X there.

59:43 speaker 2: That's what you want.
A lack of flow typing can be very annoying sometimes.

59:50 speaker 1: Lack of flow typing?I think it would be a really useful for developing types.

59:55 speaker 2: Yes,for sure.
It doesn't necessarily have to be a compiled type thing.
Yeah,but like I said,it seems understandable.
Thank you very much.However,I'm probably a bad test subject in the sense thatI will let ideas wash over me.

01:00:17 speaker 1: I will just accept it literally,

01:00:18 speaker 2: Fill in gaps.
So stuff like,you know,the nuances of the description of tea,for instance.
It's like...

01:00:28 speaker 1: That and that.Yeah.

01:00:29 speaker 2: That doesn't concern me,as long as I can understand the other things around it.

01:00:34 speaker 1: Yeah,

01:00:34 speaker 2: Yeah,yeah.So it's like...

01:00:36 speaker 1: It's very like...I feel like it's quite...
There's not very many concepts,but don't look at the typing rules first.Yes.Because if you just look at how the syntax modifies the abstract environment,it's really not rocket science.
That's what I think was really nice about the Anais paper,was that they did loads of,here's this piece of syntax and here's what the abstract form looks like before and after.

01:01:00 speaker 2: Yeah,I think having examples like that is good.
Yeah,I think lots of examples are definitely the way to go,especially in the written text,because what you do when you're explaining it on the whiteboard is you're telling me those steps.
And so it's good to encode those.
You've got a challenge,but yeah,it's not insurmountable.

01:01:27 speaker 1: Cool.And I think this will roughly form the structure of mileage reduction.
I'm just saying,I think we're getting more and more properties proven.I'm trying to go further than Roust.Yeah.Yes.
How valuable do you think an implementation would be?

01:01:50 speaker 2: Very.

01:01:51 speaker 1: Very.

01:01:55 speaker 2: I think the thing that was very wow to me about David'spresentation at least for his thesis was that he had an implementation and um i had this like odd moment right way through his presentation when i actually clocked that the thing he was working in was his own thing um i was like oh it'sworking yeah um so having that is is a very strong ace for basically saying like it works it works um and you can definitely do things it can be a simplified case

01:02:33 speaker 1: You know,

01:02:34 speaker 2: You've got eight constructs,I think you said.

01:02:37 speaker 1: Oh,well,six.
Oh,

01:02:39 speaker 2: Syntactic constructs.
So I can imagine they're similar to stuff like core and so on.
So,yeah,even if you don't opt for any syntactic sugar,because syntactic sugar is like whatever,you can make it.um being able to demonstrate i've got stuff working for this this will this could extend to anything no matter how much the language wants to grow because it's just a core construction set is a very strong case for yeah likei've done some theory i've got some actual reasoning behind this and it seems sound and also it is implementable i have parts of an implementation

01:03:31 speaker 1: I have this macro,which will take the ROS token straight now.
Oh no,

01:03:38 speaker 2: How would you do this to yourself?

01:03:39 speaker 1: Oh no,it's great!This is the best architecture I have ever come across for a compiler.It's actually fantastic.Olly Killane showed me this.Oh no.
So if I...OK,this is the thing that I'm trying to get working.
Oh,it's probably broken,isn't it?I know what state the code base is in.
It's the main system.It's your ROS code.I know.No,but there's no macro system.Look,I'll show you.Where are we?lib.rs.This is the macro,right?You take in a token stream and you return token stream.Yeah,I know.This token stream goes into a non-parser.
You don't?Oh yeah yeah yeah yeahIt goes into a non-parser!It's the same as if I'd written my...it's just someone else's token I mean instead of generating assemblyI generate Rust tokens Which is fantastic because I just...

01:04:34 speaker 2: So I'll show you what I generate I've just been way too traumatised by macros recently Yeah yeah yeah

01:04:39 speaker 1: I'm going to need to scroll up in my terminal history because I don't think this is going to be in my local versions of itYeah,look at this.So it generates unsafe rust code.
So...
This is what the program...I don't know what program it's compiling.
But,oh I think I know what it's compiling.
It's allocating a pair and assigning it to x,and then it's returning x.
And then these atoms are just the hashes of the string that they are.So this box leak,box new,is just how you do margin rest.
And then...
This Oka value add something this Oka value is 64 bits but then if you just you can specify it's a it's a c union so that is maybe values either unminitialized atom pair func pointerAnd then I can generate code like this.So the reason that value is there,that's because assignments in OCA return a unit,and that's the unit.
But the Rust compiler will get rid of it.Of course.It will get rid of all this.So I just generate Rust tokens.And then I'm going,I'm not just interpreting it,I'm actually going to like efficient assemble it.
Right,I had quite a mountain to climb with the implementation.
So I kind of,I've been like,occasionally I've been giving myself like an implementation day where I get as much done as possible,but then the rest of the time I need to see the report.

01:06:19 speaker 2: Yes,I think the...

01:06:22 speaker 1: The report sounds crucial.

01:06:23 speaker 2: The report is crucial.The implementation is nice to have.
And I think,I mean,my general strategy around this time is...

01:06:35 speaker 1: Yeah,I think we're two and a half weeks.

01:06:37 speaker 2: What you can do is you write,and you get to a point where you're submittable,and then you can do some things.
Then immediately you write about them,and you do a few more things,and immediately you print about them,and you just stop at the point,then your last snapshot is a submittable thing when you run out of time.So you don't need to worry about,I've got to get all of this finished,and then I've got to go write about all of it,and then if I don't get it done,it's just gone.Yeah.You're doing it as sort of,instead of depth first,you're iterative deepening.

01:07:09 speaker 1: Yeah,well I have started trying to put that on LaTeX.
I've written the abstract as like,I made a point of I wrote the abstract in the best case scenario.So my abstract saysI have designed,implemented.

01:07:27 speaker 2: The abstract is the last thing you wrote.

01:07:28 speaker 1: The abstract is the first thing you wrote because you want to say what you're going to do to yourself.
So I wrote my abstract.
Right.

01:07:36 speaker 2: The introduction and conclusion are also the last things you write.

01:07:40 speaker 1: That is a fucking.
Right.
I have implemented a dependently tied low level system with sound formal semantics and proofs about it being sound.
And I've implemented it in Rust.

01:08:01 speaker 2: I'm looking forward to submission when they're abstract.
This research presents Oka full stop.

01:08:09 speaker 1: Oka is an idea.
Oka has some explanation in prose.
Oka does not have some awesome ethics,nor an implementation,nor a bright future.
I like doing that because then I know what I'm aiming for.

01:08:30 speaker 2: Yes,but try and do the introduction and conclusion last.

01:08:32 speaker 1: Okay.

01:08:33 speaker 2: And they should be easiest to do.

01:08:35 speaker 1: Okay.

01:08:36 speaker 2: As long as you properly signpost out your sections,and just be woven together into the coherent start and end.

01:08:43 speaker 1: Good to know.I'm going to try to write these.

01:08:45 speaker 2: It's hard.

01:08:46 speaker 1: It's very hard.

01:08:47 speaker 2: Because you don't know what you've done yet.
You have to have your whole narrative so that you can,especially for the end of the introduction where you want your outline,which basically tells the whole story.
You can't do that until you've written the whole story.
Yeah.
Yeah,good luck.

01:09:04 speaker 1: Thank you.
Thank you,guys.
I'm curious if my whiteboard pen is now dead.DoI take it out and start working again?Of course.

01:09:30 speaker 2: We need to make it as direct as possible.
Yeah,now what's my plan for today?Oh,my plan is to make dynamic timps.
So I represent tabs.The timp node is like a Varrog's set of pairs of strings in

01:09:48 speaker 1: HTML elements.

01:09:50 speaker 2: The strings that have the HTML elements along with the tab.I'm like,I can't hide the tabs,so it needs to be a triple of strings.
Maybe a condition variable that tells me whether the term is hidden or not,and then the HTML element.

01:10:11 speaker 1: I'm going to try and do,like,you know,for this,it's just,that's just like,this is a pair,and then the syntax for application is just that.
And then I'm also going to do it where like there's only RSC size 2 pairs and then it's just write associative,but then the syntax would be that.
Which I think is pretty possible.Yeah.Especially if you're using language which doesn't block pairs.Yes.That is just the efficient way of doing that.Yes.

01:10:48 speaker 2: I'm also going to try and run pass...no that's what I was going to do,I was going to try and run pass later in the browser.I know I've already run pass in the browser since I've already done it.
Well I need an assembly highlighter.
The second J is a demanding.
Now they want to go to edit assembly too.I'll go out and pass it for assembly.
I'm not doing it by hand.I'm not hand-toping anything.

01:11:11 speaker 1: I've got stuff like that there.

Can you turn this into a structured textual explanation to the reader with headings, but keep it short. At each heading include the timestamp
