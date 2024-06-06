/*
Suppose we have a stack (really a Chapel List) and we have multiple tasks
pushing to it and popping from it in parallel.

Lists have a `parSafe` constructor so running `pushBack`s and `popBack`s in
parallel should be no problem.  But if we pop from an empty list it will still
halt execution.

I mocked up one way I think we could do this. 

My solution is to store items in the list using a nillable class and then write
my own 'nonBlockPopBack' function that uses an atomic bool to make a critical
section.

So, this:
*/

use List, Time, Random;

class R {
  var data : int;
}

var lock : atomic bool;
var taskCount : atomic int;

// Let's start our stack and add an initial item
var stack = new list(shared R, parSafe=true);
stack.pushBack(new shared R(taskCount.fetchAdd(1)));

// Let's spawn 4 tasks that keep popping from the stack and adding
// new items to it.
var numStarving : atomic int;
coforall i in 0..#4 with (ref stack) {
  var iAmStarving : bool;
  var rand = new randomStream(int);

  while(numStarving.read() < 4) {
    if(popAndPrintIt(stack)) {
      if iAmStarving { numStarving.sub(1);  iAmStarving = false; }
      // Add between 1 - 5 tasks until we've added > 100.  Yes there's a race
      // condition here where multiple tasks could reach 100 at the same time
      // but for the purpose of this example I don't care.
      for i in 0..#rand.next(1,5) {
        if(taskCount.read() < 100) {
          stack.pushBack(new shared R(taskCount.fetchAdd(1)));
        }
      }
    } else {
      if !iAmStarving { numStarving.add(1); iAmStarving = true; }
    }
  }
}

proc popAndPrintIt(ref stack) {
  var a : shared R?;
  a = nonBlockPopBack(stack);
  if(a != nil) {
    writeln(a!.data);
    return true;
  }
  return false;
}

proc nonBlockPopBack(ref stack) : shared R? {
  if !lock.testAndSet() {
    if !stack.isEmpty() {
      const ref val = stack.popBack();
      lock.clear();
      return val;
    }
    lock.clear();
    return nil;
  }
  return nil;
}

