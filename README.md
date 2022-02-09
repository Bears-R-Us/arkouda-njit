## Purpose
This is an external repo to build Graph related functionality for `Arkouda`
(see https://github.com/Bears-R-Us/Arkouda)

## Generate Server Code
To generate the server code run the `server-config.py` file.
It will generate commands which you can pipe to a shell for execution which
will build the Arkouda server including the Graph server functions.

```bash
# Print usage instructions
python server-config.py --help

# Sample invocation
python server-config.py --arkouda=$HOME/projects/arkouda

# Sample execution
python server-config.py --arkouda=$HOME/projects/arkouda | bash
```

## Client code
TODO
