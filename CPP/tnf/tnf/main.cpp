#include <iostream>
using namespace std;

class Term {
};

class None : Term {
  
};

class Var : Term {
  Term val=(Term)*this;
};

class Atomic : Term {
  string val;
};

class Pair : Term {
  Term* left;
  Term* right;
};


//Term :: *Term deref() {
//  return this;
//};

int main () {
  string s="hello";
  cout << s <<  "\n";
  cout << sizeof(Pair) <<  "\n";
 
  return 0;
};

