// Configuration schema
package config

#Config: {
    name:     string
    replicas: int & >=1
    port:     int & >=1 & <=65535
    env:      string
}
