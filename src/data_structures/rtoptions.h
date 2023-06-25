/*------------------------------------------------------------------------*/

// Relying on compile-time configuration, we have very few run-time options.

struct options
{
  bool ascii;			// Use ASCII proof format.
#ifdef LOGGING
  bool logging;			// Print logging messages.
#endif
  unsigned verbose;		// Verbose level for messages 0..4.
};

