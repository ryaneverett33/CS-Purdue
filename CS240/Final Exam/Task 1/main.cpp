/*******************************************************
 * For the detailed Task description, go to MyVector.h *
 *******************************************************/

#include <iostream>
#include <exception>
#include <stdlib.h>
#include "MyVector.h"
#include "MyException.h"

using namespace std;

int main(int argc, char *argv[])
{
  MyVector    *V = new MyVector(100);
  int         choice;
  
  cout << endl << "A Vector has been already created for your convenience." << endl;
  while (1)
  {
      cout << endl << "What operation you would like to perform?"<< endl;
      cout << "1. Get the size of the vector\n";
      cout << "2. Get the value at a index\n";
      cout << "3. Set the value at a index\n";
      cout << "4. Print the whole vector\n";
      cout << "5. Exit\n";
      cin >> choice;

      switch(choice)
      {
        case 1:
          cout << "Vector size: " << V->get_size() << endl;
          break;
       
        case 2:
        {
          int   index, value;
          cout <<"Enter the index to fetch the value from: "; 
          cin >> index; 
          cout << endl;
          try
          {
            if (V->get_num_at_idx(index, &value))
              cout << "Value at " << index << " is " << value << endl;
            else
              cout << "Invalid input" << endl;
          }
          catch (MyException &e)
          {
            cout << e.what();
          }
          break;
        }  
        
        case 3:
        {
          int   index, value;

          cout <<"Enter the index: "; 
          cin >> index; cout << endl;
          cout <<"Enter the value: "; 
          cin >> value; cout << endl;

          try
          {
            if (V->set_num_at_idx(index, value))
              cout << "Value set successfully" << endl;
            else
              cout << "Invalid input" << endl;
          }
          catch (MyException &e)
          {
            cout << e.what();
          }
          break;
        }
        
        case 4:
          V->print();
          break;

        case 5:
          delete V;
          return 0;
        
        default:
          break;
      }
  }
}
