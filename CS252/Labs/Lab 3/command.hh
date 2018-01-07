#ifndef command_h
#define command_h

#include "simpleCommand.hh"

// Command Data Structure

struct Command {
  int _numOfAvailableSimpleCommands;
  int _numOfSimpleCommands;
  SimpleCommand ** _simpleCommands;
  char * _outFile;
  char * _inFile;
  char * _errFile;
  bool _errAppend = false;
  bool _outAppend = false;
  bool _isSource = false;
  int _background;
  int _lastCode = 2;
  int _lastBackground = -1;
  int _shellPid = -1;
  char * _lastArgument;
  char * _shellLoc;
  char * _shellName;

  void prompt();
  void print();
  void execute();
  void clear();
  void sighandle(int);
  void zombie(int);

  Command();
  void insertSimpleCommand( SimpleCommand * simpleCommand );
  void storeLastArgument(SimpleCommand *command);

  static Command _currentCommand;
  static SimpleCommand *_currentSimpleCommand;
};

#endif
