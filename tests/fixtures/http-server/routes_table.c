#include "http_server.h"

/* A separate translation unit preserves table loads without disabling optimization. */
const struct http_route http_routes[2] = {
    {"/health", http_health_handler},
    {"/metrics", http_metrics_handler},
};
